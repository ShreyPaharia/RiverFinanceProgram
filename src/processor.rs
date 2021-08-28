//! Program state processor

use crate::constraints::{Constraints, SWAP_CONSTRAINTS};
use crate::{
    error::StreamError,
    instruction::{
        DepositToken, Initialize,
        SwapInstruction, WithdrawToken,
        StartStream,
    },
    state::{StreamState, StreamV1, StreamVersion},
};
use num_traits::FromPrimitive;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    decode_error::DecodeError,
    entrypoint::ProgramResult,
    msg,
    program::invoke_signed,
    program_error::{PrintProgramError, ProgramError},
    program_option::COption,
    program_pack::Pack,
    pubkey::Pubkey,
};
use std::convert::TryInto;

/// Program state handler.
pub struct Processor {}
impl Processor {
    /// Unpacks a spl_token `Account`.
    pub fn unpack_tokenccount(
        account_info: &AccountInfo,
        token_program_id: &Pubkey,
    ) -> Result<spl_token::state::Account, StreamError> {
        if account_info.owner != token_program_id {
            Err(StreamError::IncorrectTokenProgramId)
        } else {
            spl_token::state::Account::unpack(&account_info.data.borrow())
                .map_err(|_| StreamError::ExpectedAccount)
        }
    }

    /// Unpacks a spl_token `Mint`.
    pub fn unpack_mint(
        account_info: &AccountInfo,
        token_program_id: &Pubkey,
    ) -> Result<spl_token::state::Mint, StreamError> {
        if account_info.owner != token_program_id {
            Err(StreamError::IncorrectTokenProgramId)
        } else {
            spl_token::state::Mint::unpack(&account_info.data.borrow())
                .map_err(|_| StreamError::ExpectedMint)
        }
    }

    /// Calculates the authority id by generating a program address.
    pub fn authority_id(
        program_id: &Pubkey,
        my_info: &Pubkey,
        nonce: u8,
    ) -> Result<Pubkey, StreamError> {
        Pubkey::create_program_address(&[&my_info.to_bytes()[..32], &[nonce]], program_id)
            .or(Err(StreamError::InvalidProgramAddress))
    }

    /// Issue a spl_token `Burn` instruction.
    pub fn token_burn<'a>(
        swap: &Pubkey,
        token_program: AccountInfo<'a>,
        burn_account: AccountInfo<'a>,
        mint: AccountInfo<'a>,
        authority: AccountInfo<'a>,
        nonce: u8,
        amount: u64,
    ) -> Result<(), ProgramError> {
        let swap_bytes = swap.to_bytes();
        let authority_signature_seeds = [&swap_bytes[..32], &[nonce]];
        let signers = &[&authority_signature_seeds[..]];

        let ix = spl_token::instruction::burn(
            token_program.key,
            burn_account.key,
            mint.key,
            authority.key,
            &[],
            amount,
        )?;

        invoke_signed(
            &ix,
            &[burn_account, mint, authority, token_program],
            signers,
        )
    }

    /// Issue a spl_token `MintTo` instruction.
    pub fn token_mint_to<'a>(
        swap: &Pubkey,
        token_program: AccountInfo<'a>,
        mint: AccountInfo<'a>,
        destination: AccountInfo<'a>,
        authority: AccountInfo<'a>,
        nonce: u8,
        amount: u64,
    ) -> Result<(), ProgramError> {
        let swap_bytes = swap.to_bytes();
        let authority_signature_seeds = [&swap_bytes[..32], &[nonce]];
        let signers = &[&authority_signature_seeds[..]];
        let ix = spl_token::instruction::mint_to(
            token_program.key,
            mint.key,
            destination.key,
            authority.key,
            &[],
            amount,
        )?;

        invoke_signed(&ix, &[mint, destination, authority, token_program], signers)
    }

    /// Issue a spl_token `Transfer` instruction.
    pub fn token_transfer<'a>(
        swap: &Pubkey,
        token_program: AccountInfo<'a>,
        source: AccountInfo<'a>,
        destination: AccountInfo<'a>,
        authority: AccountInfo<'a>,
        nonce: u8,
        amount: u64,
    ) -> Result<(), ProgramError> {
        let swap_bytes = swap.to_bytes();
        let authority_signature_seeds = [&swap_bytes[..32], &[nonce]];
        let signers = &[&authority_signature_seeds[..]];
        let ix = spl_token::instruction::transfer(
            token_program.key,
            source.key,
            destination.key,
            authority.key,
            &[],
            amount,
        )?;
        invoke_signed(
            &ix,
            &[source, destination, authority, token_program],
            signers,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn check_accounts(
        token_swap: &dyn StreamState,
        program_id: &Pubkey,
        swap_account_info: &AccountInfo,
        authority_info: &AccountInfo,
        token_info: &AccountInfo,
        stream_token_mint_info: &AccountInfo,
        token_program_info: &AccountInfo,
        user_token_info: Option<&AccountInfo>,
        stream_fee_account_info: Option<&AccountInfo>,
    ) -> ProgramResult {
        if swap_account_info.owner != program_id {
            return Err(ProgramError::IncorrectProgramId);
        }
        if *authority_info.key
            != Self::authority_id(program_id, swap_account_info.key, token_swap.nonce())?
        {
            return Err(StreamError::InvalidProgramAddress.into());
        }
        if *token_info.key != *token_swap.token_account() {
            return Err(StreamError::IncorrectSwapAccount.into());
        }
        if *stream_token_mint_info.key != *token_swap.stream_token_mint() {
            return Err(StreamError::IncorrectPoolMint.into());
        }
        if *token_program_info.key != *token_swap.token_program_id() {
            return Err(StreamError::IncorrectTokenProgramId.into());
        }
        if let Some(user_token_info) = user_token_info {
            if token_info.key == user_token_info.key {
                return Err(StreamError::InvalidInput.into());
            }
        }
        if let Some(stream_fee_account_info) = stream_fee_account_info {
            if *stream_fee_account_info.key != *token_swap.stream_fee_account() {
                return Err(StreamError::IncorrectFeeAccount.into());
            }
        }
        Ok(())
    }

    /// Processes an [Initialize](enum.Instruction.html).
    pub fn process_initialize(
        program_id: &Pubkey,
        nonce: u8,
        accounts: &[AccountInfo],
        swap_constraints: &Option<Constraints>,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let swap_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;
        let token_info = next_account_info(account_info_iter)?;
        let stream_token_mint_info = next_account_info(account_info_iter)?;
        let fee_account_info = next_account_info(account_info_iter)?;
        let destination_info = next_account_info(account_info_iter)?;
        let token_program_info = next_account_info(account_info_iter)?;

        let token_program_id = *token_program_info.key;
        if StreamVersion::is_initialized(&swap_info.data.borrow()) {
            return Err(StreamError::AlreadyInUse.into());
        }

        if *authority_info.key != Self::authority_id(program_id, swap_info.key, nonce)? {
            return Err(StreamError::InvalidProgramAddress.into());
        }
        let token = Self::unpack_tokenccount(token_info, &token_program_id)?;
        let fee_account = Self::unpack_tokenccount(fee_account_info, &token_program_id)?;
        let destination = Self::unpack_tokenccount(destination_info, &token_program_id)?;
        let stream_token_mint = Self::unpack_mint(stream_token_mint_info, &token_program_id)?;
        if *authority_info.key != token.owner {
            return Err(StreamError::InvalidOwner.into());
        }
        if *authority_info.key == destination.owner {
            return Err(StreamError::InvalidOutputOwner.into());
        }
        if *authority_info.key == fee_account.owner {
            return Err(StreamError::InvalidOutputOwner.into());
        }
        if COption::Some(*authority_info.key) != stream_token_mint.mint_authority {
            return Err(StreamError::InvalidOwner.into());
        }

        if token.amount == 0 {
            return Err(StreamError::EmptySupply.into());
        }
      
        if token.delegate.is_some() {
            return Err(StreamError::InvalidDelegate.into());
        }

        if token.close_authority.is_some() {
            return Err(StreamError::InvalidCloseAuthority.into());
        }

        if stream_token_mint.supply != 0 {
            return Err(StreamError::InvalidSupply.into());
        }
        if stream_token_mint.freeze_authority.is_some() {
            return Err(StreamError::InvalidFreezeAuthority.into());
        }
        if *stream_token_mint_info.key != fee_account.mint {
            return Err(StreamError::IncorrectPoolMint.into());
        }

        if let Some(swap_constraints) = swap_constraints {
            let owner_key = swap_constraints
                .owner_key
                .parse::<Pubkey>()
                .map_err(|_| StreamError::InvalidOwner)?;
            if fee_account.owner != owner_key {
                return Err(StreamError::InvalidOwner.into());
            }
        }

        //TODO: Check this
        let initial_amount = 1000u128;

        Self::token_mint_to(
            swap_info.key,
            token_program_info.clone(),
            stream_token_mint_info.clone(),
            destination_info.clone(),
            authority_info.clone(),
            nonce,
            to_u64(initial_amount)?,
        )?;

        let obj = StreamVersion::StreamV1(StreamV1 {
            is_initialized: true,
            nonce,
            token_program_id,
            token: *token_info.key,
            stream_token_mint: *stream_token_mint_info.key,
            token_mint: token.mint,
            stream_fee_account: *fee_account_info.key,
        });
        StreamVersion::pack(obj, &mut swap_info.data.borrow_mut())?;
        Ok(())
    }

    /// Processes an [DepositToken](enum.Instruction.html).
    pub fn process_deposit_token(
        program_id: &Pubkey,
        tokenamount: u64,
        accounts: &[AccountInfo],
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let swap_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;
        let user_transfer_authority_info = next_account_info(account_info_iter)?;
        let source_a_info = next_account_info(account_info_iter)?;
        let token_info = next_account_info(account_info_iter)?;
        let stream_token_mint_info = next_account_info(account_info_iter)?;
        let dest_info = next_account_info(account_info_iter)?;
        let token_program_info = next_account_info(account_info_iter)?;

        let token_swap = StreamVersion::unpack(&swap_info.data.borrow())?;

        Self::check_accounts(
            token_swap.as_ref(),
            program_id,
            swap_info,
            authority_info,
            token_info,
            stream_token_mint_info,
            token_program_info,
            Some(source_a_info),
            None,
        )?;

        let token = Self::unpack_tokenccount(token_info, token_swap.token_program_id())?;
        let stream_token_mint = Self::unpack_mint(stream_token_mint_info, token_swap.token_program_id())?;
        let current_stream_token_mint_supply = to_u128(stream_token_mint.supply)?;
        let (tokenamount, stream_token_mint_supply) = if current_stream_token_mint_supply > 0 {
            (to_u128(tokenamount)?, current_stream_token_mint_supply)
        } else {
            // TODO:Check this
            // (calculator.new_pool_supply(), calculator.new_pool_supply())
            (to_u128(token.amount)?,current_stream_token_mint_supply)
        };

        let tokenamount = to_u64(tokenamount)?;
        let token_amount = token.amount;
        if token_amount < tokenamount {
            return Err(StreamError::InsufficientFunds.into());
        }
        if token_amount == 0 {
            return Err(StreamError::ZeroTradingTokens.into());
        }


        Self::token_transfer(
            swap_info.key,
            token_program_info.clone(),
            source_a_info.clone(),
            token_info.clone(),
            user_transfer_authority_info.clone(),
            token_swap.nonce(),
            tokenamount,
        )?;

        Self::token_mint_to(
            swap_info.key,
            token_program_info.clone(),
            stream_token_mint_info.clone(),
            dest_info.clone(),
            authority_info.clone(),
            token_swap.nonce(),
            tokenamount,
        )?;

        Ok(())
    }

    /// Processes an [WithdrawToken](enum.Instruction.html).
    pub fn process_withdraw_token(
        program_id: &Pubkey,
        tokenamount: u64,
        accounts: &[AccountInfo],
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let swap_info = next_account_info(account_info_iter)?;
        let authority_info = next_account_info(account_info_iter)?;
        let user_transfer_authority_info = next_account_info(account_info_iter)?;
        let stream_token_mint_info = next_account_info(account_info_iter)?;
        let source_info = next_account_info(account_info_iter)?;
        let token_info = next_account_info(account_info_iter)?;
        let dest_token_info = next_account_info(account_info_iter)?;
        let stream_fee_account_info = next_account_info(account_info_iter)?;
        let token_program_info = next_account_info(account_info_iter)?;

        let token_swap = StreamVersion::unpack(&swap_info.data.borrow())?;
        Self::check_accounts(
            token_swap.as_ref(),
            program_id,
            swap_info,
            authority_info,
            token_info,
            stream_token_mint_info,
            token_program_info,
            Some(dest_token_info),
            Some(stream_fee_account_info),
        )?;

        let token = Self::unpack_tokenccount(token_info, token_swap.token_program_id())?;
        let stream_token_mint = Self::unpack_mint(stream_token_mint_info, token_swap.token_program_id())?;

        let withdraw_fee: u128 = if *stream_fee_account_info.key == *source_info.key {
            // withdrawing from the fee account, don't assess withdraw fee
            0
        } else {
            //Fees always 0
            0
            // token_swap
            //     .fees()
            //     .owner_withdraw_fee(to_u128(tokenamount)?)
            //     .ok_or(StreamError::FeeCalculationFailure)?
        };
        let tokenamount = to_u128(tokenamount)?
            .checked_sub(withdraw_fee)
            .ok_or(StreamError::CalculationFailure)?;

        let token_amount = token.amount;

        if token_amount == 0 && token.amount != 0 {
            return Err(StreamError::ZeroTradingTokens.into());
        }
    
        let tokenamount = to_u64(tokenamount)?;
        if withdraw_fee > 0 {
            Self::token_transfer(
                swap_info.key,
                token_program_info.clone(),
                source_info.clone(),
                stream_fee_account_info.clone(),
                user_transfer_authority_info.clone(),
                token_swap.nonce(),
                to_u64(withdraw_fee)?,
            )?;
        }
        Self::token_burn(
            swap_info.key,
            token_program_info.clone(),
            source_info.clone(),
            stream_token_mint_info.clone(),
            user_transfer_authority_info.clone(),
            token_swap.nonce(),
            tokenamount,
        )?;

        if token_amount > 0 {
            Self::token_transfer(
                swap_info.key,
                token_program_info.clone(),
                token_info.clone(),
                dest_token_info.clone(),
                authority_info.clone(),
                token_swap.nonce(),
                tokenamount,
            )?;
        }

        Ok(())
    }

        /// Processes an [DepositToken](enum.Instruction.html).
        pub fn process_start_stream(
            program_id: &Pubkey,
            tokenamount: u64,
            accounts: &[AccountInfo],
        ) -> ProgramResult {
            let account_info_iter = &mut accounts.iter();
            let stream_token_info = next_account_info(account_info_iter)?;
            let authority_info = next_account_info(account_info_iter)?;
            let user_transfer_authority_info = next_account_info(account_info_iter)?;
            let source_a_info = next_account_info(account_info_iter)?;
            let token_info = next_account_info(account_info_iter)?;
            let stream_token_mint_info = next_account_info(account_info_iter)?;
            let receiver_info = next_account_info(account_info_iter)?;
            let token_program_info = next_account_info(account_info_iter)?;
    
            let stream_token_data = StreamVersion::unpack(&stream_token_info.data.borrow())?;
    
            Self::check_accounts(
                stream_token_data.as_ref(),
                program_id,
                stream_token_info,
                authority_info,
                token_info,
                stream_token_mint_info,
                token_program_info,
                Some(source_a_info),
                None,
            )?;
    
            let token = Self::unpack_tokenccount(token_info, stream_token_data.token_program_id())?;
            let stream_token_mint = Self::unpack_mint(stream_token_mint_info, stream_token_data.token_program_id())?;
            let current_stream_token_mint_supply = to_u128(stream_token_mint.supply)?;
            let (tokenamount, stream_token_mint_supply) = if current_stream_token_mint_supply > 0 {
                (to_u128(tokenamount)?, current_stream_token_mint_supply)
            } else {
                // TODO:Check this
                // (calculator.new_pool_supply(), calculator.new_pool_supply())
                (to_u128(token.amount)?,current_stream_token_mint_supply)
            };
    
            let tokenamount = to_u64(tokenamount)?;
            let token_amount = token.amount;
            if token_amount < tokenamount {
                return Err(StreamError::InsufficientFunds.into());
            }
            if token_amount == 0 {
                return Err(StreamError::ZeroTradingTokens.into());
            }
    
    
            // Self::token_transfer(
            //     swap_info.key,
            //     token_program_info.clone(),
            //     source_a_info.clone(),
            //     token_info.clone(),
            //     user_transfer_authority_info.clone(),
            //     stream_token_data.nonce(),
            //     tokenamount,
            // )?;
    
            // Self::token_mint_to(
            //     swap_info.key,
            //     token_program_info.clone(),
            //     stream_token_mint_info.clone(),
            //     dest_info.clone(),
            //     authority_info.clone(),
            //     stream_token_data.nonce(),
            //     tokenamount,
            // )?;

            // let obj = StreamVersion::StreamV1(StreamV1 {
            //     is_initialized: true,
            //     nonce,
            //     token_program_id,
            //     token: *token_info.key,
            //     stream_token_mint: *stream_token_mint_info.key,
            //     token_mint: token.mint,
            //     stream_fee_account: *fee_account_info.key,
            // });
            // StreamVersion::pack(obj, &mut swap_info.data.borrow_mut())?;
    
            Ok(())
        }

    /// Processes an [Instruction](enum.Instruction.html).
    pub fn process(program_id: &Pubkey, accounts: &[AccountInfo], input: &[u8]) -> ProgramResult {
        Self::process_with_constraints(program_id, accounts, input, &SWAP_CONSTRAINTS)
    }

    /// Processes an instruction given extra constraint
    pub fn process_with_constraints(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        input: &[u8],
        swap_constraints: &Option<Constraints>,
    ) -> ProgramResult {
        let instruction = SwapInstruction::unpack(input)?;
        match instruction {
            SwapInstruction::Initialize(Initialize {
                nonce
            }) => {
                msg!("Instruction: Init");
                Self::process_initialize(
                    program_id,
                    nonce,
                    accounts,
                    swap_constraints,
                )
            }
            SwapInstruction::DepositToken(DepositToken {
                tokenamount,
            }) => {
                msg!("Instruction: DepositToken");
                Self::process_deposit_token(
                    program_id,
                    tokenamount,
                    accounts,
                )
            }
            SwapInstruction::WithdrawToken(WithdrawToken {
                tokenamount,
            }) => {
                msg!("Instruction: WithdrawToken");
                Self::process_withdraw_token(
                    program_id,
                    tokenamount,
                    accounts,
                )
            }
            SwapInstruction::StartStream(StartStream {
                tokenamount,
            }) => {
                msg!("Instruction: StartStream");
                Self::process_start_stream(
                    program_id,
                    tokenamount,
                    accounts,
                )
            }
           
        }
    }
}

impl PrintProgramError for StreamError {
    fn print<E>(&self)
    where
        E: 'static + std::error::Error + DecodeError<E> + PrintProgramError + FromPrimitive,
    {
        match self {
            StreamError::AlreadyInUse => msg!("Error: Swap account already in use"),
            StreamError::InvalidProgramAddress => {
                msg!("Error: Invalid program address generated from nonce and key")
            }
            StreamError::InvalidOwner => {
                msg!("Error: The input account owner is not the program address")
            }
            StreamError::InvalidOutputOwner => {
                msg!("Error: Output pool account owner cannot be the program address")
            }
            StreamError::ExpectedMint => msg!("Error: Deserialized account is not an SPL Token mint"),
            StreamError::ExpectedAccount => {
                msg!("Error: Deserialized account is not an SPL Token account")
            }
            StreamError::EmptySupply => msg!("Error: Input token account empty"),
            StreamError::InvalidSupply => msg!("Error: Pool token mint has a non-zero supply"),
            StreamError::RepeatedMint => msg!("Error: Swap input token accounts have the same mint"),
            StreamError::InvalidDelegate => msg!("Error: Token account has a delegate"),
            StreamError::InvalidInput => msg!("Error: InvalidInput"),
            StreamError::IncorrectSwapAccount => {
                msg!("Error: Address of the provided swap token account is incorrect")
            }
            StreamError::IncorrectPoolMint => {
                msg!("Error: Address of the provided pool token mint is incorrect")
            }
            StreamError::InvalidOutput => msg!("Error: InvalidOutput"),
            StreamError::CalculationFailure => msg!("Error: CalculationFailure"),
            StreamError::InvalidInstruction => msg!("Error: InvalidInstruction"),
            StreamError::ExceededSlippage => {
                msg!("Error: Swap instruction exceeds desired slippage limit")
            }
            StreamError::InvalidCloseAuthority => msg!("Error: Token account has a close authority"),
            StreamError::InvalidFreezeAuthority => {
                msg!("Error: Pool token mint has a freeze authority")
            }
            StreamError::IncorrectFeeAccount => msg!("Error: Pool fee token account incorrect"),
            StreamError::ZeroTradingTokens => {
                msg!("Error: Given pool token amount results in zero trading tokens")
            }
            StreamError::FeeCalculationFailure => msg!(
                "Error: The fee calculation failed due to overflow, underflow, or unexpected 0"
            ),
            StreamError::ConversionFailure => msg!("Error: Conversion to or from u64 failed."),
            StreamError::InvalidFee => {
                msg!("Error: The provided fee does not match the program owner's constraints")
            }
            StreamError::IncorrectTokenProgramId => {
                msg!("Error: The provided token program does not match the token program expected by the swap")
            }
            StreamError::UnsupportedCurveType => {
                msg!("Error: The provided curve type is not supported by the program owner")
            }
            StreamError::InvalidCurve => {
                msg!("Error: The provided curve parameters are invalid")
            }
            StreamError::InsufficientFunds => {
                msg!("Error: The balance of input tokens is not enough")
            }
            StreamError::UnsupportedCurveOperation => {
                msg!("Error: The operation cannot be performed on the given curve")
            }
        }
    }
}

fn to_u128(val: u64) -> Result<u128, StreamError> {
    val.try_into().map_err(|_| StreamError::ConversionFailure)
}

fn to_u64(val: u128) -> Result<u64, StreamError> {
    val.try_into().map_err(|_| StreamError::ConversionFailure)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instruction::{
            deposit_token, initialize,
            withdraw_token,
        },
    };
    use solana_program::{instruction::Instruction, program_stubs, rent::Rent};
    use solana_sdk::account::{create_account_for_test, create_is_signer_account_infos, Account};
    use spl_token::{
        error::TokenError,
        instruction::{
            approve, initialize_account, initialize_mint, mint_to, revoke, set_authority,
            AuthorityType,
        },
    };

    // Test program id for the swap program.
    const SWAP_PROGRAM_ID: Pubkey = Pubkey::new_from_array([2u8; 32]);

    struct TestSyscallStubs {}
    impl program_stubs::SyscallStubs for TestSyscallStubs {
        fn sol_invoke_signed(
            &self,
            instruction: &Instruction,
            account_infos: &[AccountInfo],
            signers_seeds: &[&[&[u8]]],
        ) -> ProgramResult {
            msg!("TestSyscallStubs::sol_invoke_signed()");

            let mut new_account_infos = vec![];

            // mimic check for token program in accounts
            if !account_infos.iter().any(|x| *x.key == spl_token::id()) {
                return Err(ProgramError::InvalidAccountData);
            }

            for meta in instruction.accounts.iter() {
                for account_info in account_infos.iter() {
                    if meta.pubkey == *account_info.key {
                        let mut new_account_info = account_info.clone();
                        for seeds in signers_seeds.iter() {
                            let signer =
                                Pubkey::create_program_address(seeds, &SWAP_PROGRAM_ID).unwrap();
                            if *account_info.key == signer {
                                new_account_info.is_signer = true;
                            }
                        }
                        new_account_infos.push(new_account_info);
                    }
                }
            }

            spl_token::processor::Processor::process(
                &instruction.program_id,
                &new_account_infos,
                &instruction.data,
            )
        }
    }

    fn test_syscall_stubs() {
        use std::sync::Once;
        static ONCE: Once = Once::new();

        ONCE.call_once(|| {
            program_stubs::set_syscall_stubs(Box::new(TestSyscallStubs {}));
        });
    }

    struct SwapAccountInfo {
        nonce: u8,
        authority_key: Pubkey,
        swap_key: Pubkey,
        swap_account: Account,
        stream_token_mint_key: Pubkey,
        stream_token_mint_account: Account,
        pool_fee_key: Pubkey,
        stream_fee_account: Account,
        pool_token_key: Pubkey,
        pool_tokenccount: Account,
        token_key: Pubkey,
        token_account: Account,
        token_mint_key: Pubkey,
        token_mint_account: Account,
    }

    impl SwapAccountInfo {
        pub fn new(
            user_key: &Pubkey,
            token_amount: u64,
        ) -> Self {
            let swap_key = Pubkey::new_unique();
            let swap_account = Account::new(0, StreamVersion::LATEST_LEN, &SWAP_PROGRAM_ID);
            let (authority_key, nonce) =
                Pubkey::find_program_address(&[&swap_key.to_bytes()[..]], &SWAP_PROGRAM_ID);

            let (stream_token_mint_key, mut stream_token_mint_account) =
                create_mint(&spl_token::id(), &authority_key, None);
            let (pool_token_key, pool_tokenccount) = mint_token(
                &spl_token::id(),
                &stream_token_mint_key,
                &mut stream_token_mint_account,
                &authority_key,
                user_key,
                0,
            );
            let (pool_fee_key, stream_fee_account) = mint_token(
                &spl_token::id(),
                &stream_token_mint_key,
                &mut stream_token_mint_account,
                &authority_key,
                user_key,
                0,
            );
            let (token_mint_key, mut token_mint_account) =
                create_mint(&spl_token::id(), user_key, None);
            let (token_key, token_account) = mint_token(
                &spl_token::id(),
                &token_mint_key,
                &mut token_mint_account,
                user_key,
                &authority_key,
                token_amount,
            );

            SwapAccountInfo {
                nonce,
                authority_key,
                swap_key,
                swap_account,
                stream_token_mint_key,
                stream_token_mint_account,
                pool_fee_key,
                stream_fee_account,
                pool_token_key,
                pool_tokenccount,
                token_key,
                token_account,
                token_mint_key,
                token_mint_account,
            }
        }

        pub fn initialize_swap(&mut self) -> ProgramResult {
            do_process_instruction(
                initialize(
                    &SWAP_PROGRAM_ID,
                    &spl_token::id(),
                    &self.swap_key,
                    &self.authority_key,
                    &self.token_key,
                    &self.stream_token_mint_key,
                    &self.pool_fee_key,
                    &self.pool_token_key,
                    self.nonce,
                )
                .unwrap(),
                vec![
                    &mut self.swap_account,
                    &mut Account::default(),
                    &mut self.token_account,
                    &mut self.stream_token_mint_account,
                    &mut self.stream_fee_account,
                    &mut self.pool_tokenccount,
                    &mut Account::default(),
                ],
            )
        }

        pub fn setup_tokenccounts(
            &mut self,
            mint_owner: &Pubkey,
            account_owner: &Pubkey,
            a_amount: u64,
            pool_amount: u64,
        ) -> (Pubkey, Account, Pubkey, Account) {
            let (token_key, token_account) = mint_token(
                &spl_token::id(),
                &self.token_mint_key,
                &mut self.token_mint_account,
                mint_owner,
                account_owner,
                a_amount,
            );
            let (pool_key, pool_account) = mint_token(
                &spl_token::id(),
                &self.stream_token_mint_key,
                &mut self.stream_token_mint_account,
                &self.authority_key,
                account_owner,
                pool_amount,
            );
            (
                token_key,
                token_account,
                pool_key,
                pool_account,
            )
        }

        fn get_tokenccount(&self, account_key: &Pubkey) -> &Account {
            if *account_key == self.token_key {
                return &self.token_account;
            } 
            panic!("Could not find matching swap token account");
        }

        fn set_tokenccount(&mut self, account_key: &Pubkey, account: Account) {
            if *account_key == self.token_key {
                self.token_account = account;
                return;
            } 
            panic!("Could not find matching swap token account");
        }


        #[allow(clippy::too_many_arguments)]
        pub fn deposit_token(
            &mut self,
            depositor_key: &Pubkey,
            depositor_token_key: &Pubkey,
            mut depositor_token_account: &mut Account,
            depositor_pool_key: &Pubkey,
            mut depositor_pool_account: &mut Account,
            tokenamount: u64,
        ) -> ProgramResult {
            let user_transfer_authority = Pubkey::new_unique();
            do_process_instruction(
                approve(
                    &spl_token::id(),
                    depositor_token_key,
                    &user_transfer_authority,
                    depositor_key,
                    &[],
                    tokenamount,
                )
                .unwrap(),
                vec![
                    &mut depositor_token_account,
                    &mut Account::default(),
                    &mut Account::default(),
                ],
            )
            .unwrap();

            do_process_instruction(
                deposit_token(
                    &SWAP_PROGRAM_ID,
                    &spl_token::id(),
                    &self.swap_key,
                    &self.authority_key,
                    &user_transfer_authority,
                    depositor_token_key,
                    &self.token_key,
                    &self.stream_token_mint_key,
                    depositor_pool_key,
                    DepositToken {
                        tokenamount,
                    },
                )
                .unwrap(),
                vec![
                    &mut self.swap_account,
                    &mut Account::default(),
                    &mut Account::default(),
                    &mut depositor_token_account,
                    &mut self.token_account,
                    &mut self.stream_token_mint_account,
                    &mut depositor_pool_account,
                    &mut Account::default(),
                ],
            )
        }

        #[allow(clippy::too_many_arguments)]
        pub fn withdraw_token(
            &mut self,
            user_key: &Pubkey,
            pool_key: &Pubkey,
            mut pool_account: &mut Account,
            token_key: &Pubkey,
            mut token_account: &mut Account,
            tokenamount: u64,
        ) -> ProgramResult {
            let user_transfer_authority_key = Pubkey::new_unique();
            // approve user transfer authority to take out pool tokens
            do_process_instruction(
                approve(
                    &spl_token::id(),
                    pool_key,
                    &user_transfer_authority_key,
                    user_key,
                    &[],
                    tokenamount,
                )
                .unwrap(),
                vec![
                    &mut pool_account,
                    &mut Account::default(),
                    &mut Account::default(),
                ],
            )
            .unwrap();

            // withdraw token a and b correctly
            do_process_instruction(
                withdraw_token(
                    &SWAP_PROGRAM_ID,
                    &spl_token::id(),
                    &self.swap_key,
                    &self.authority_key,
                    &user_transfer_authority_key,
                    &self.stream_token_mint_key,
                    &self.pool_fee_key,
                    pool_key,
                    &self.token_key,
                    token_key,
                    WithdrawToken {
                        tokenamount,
                    },
                )
                .unwrap(),
                vec![
                    &mut self.swap_account,
                    &mut Account::default(),
                    &mut Account::default(),
                    &mut self.stream_token_mint_account,
                    &mut pool_account,
                    &mut self.token_account,
                    &mut token_account,
                    &mut self.stream_fee_account,
                    &mut Account::default(),
                ],
            )
        }
    }

    fn mint_minimum_balance() -> u64 {
        Rent::default().minimum_balance(spl_token::state::Mint::get_packed_len())
    }

    fn account_minimum_balance() -> u64 {
        Rent::default().minimum_balance(spl_token::state::Account::get_packed_len())
    }

    fn do_process_instruction_with_fee_constraints(
        instruction: Instruction,
        accounts: Vec<&mut Account>,
        swap_constraints: &Option<Constraints>,
    ) -> ProgramResult {
        test_syscall_stubs();

        // approximate the logic in the actual runtime which runs the instruction
        // and only updates accounts if the instruction is successful
        let mut account_clones = accounts.iter().map(|x| (*x).clone()).collect::<Vec<_>>();
        let mut meta = instruction
            .accounts
            .iter()
            .zip(account_clones.iter_mut())
            .map(|(account_meta, account)| (&account_meta.pubkey, account_meta.is_signer, account))
            .collect::<Vec<_>>();
        let mut account_infos = create_is_signer_account_infos(&mut meta);
        let res = if instruction.program_id == SWAP_PROGRAM_ID {
            Processor::process_with_constraints(
                &instruction.program_id,
                &account_infos,
                &instruction.data,
                swap_constraints,
            )
        } else {
            spl_token::processor::Processor::process(
                &instruction.program_id,
                &account_infos,
                &instruction.data,
            )
        };

        if res.is_ok() {
            let mut account_metas = instruction
                .accounts
                .iter()
                .zip(accounts)
                .map(|(account_meta, account)| (&account_meta.pubkey, account))
                .collect::<Vec<_>>();
            for account_info in account_infos.iter_mut() {
                for account_meta in account_metas.iter_mut() {
                    if account_info.key == account_meta.0 {
                        let account = &mut account_meta.1;
                        account.owner = *account_info.owner;
                        account.lamports = **account_info.lamports.borrow();
                        account.data = account_info.data.borrow().to_vec();
                    }
                }
            }
        }
        res
    }

    fn do_process_instruction(
        instruction: Instruction,
        accounts: Vec<&mut Account>,
    ) -> ProgramResult {
        do_process_instruction_with_fee_constraints(instruction, accounts, &SWAP_CONSTRAINTS)
    }

    fn mint_token(
        program_id: &Pubkey,
        mint_key: &Pubkey,
        mut mint_account: &mut Account,
        mint_authority_key: &Pubkey,
        account_owner_key: &Pubkey,
        amount: u64,
    ) -> (Pubkey, Account) {
        let account_key = Pubkey::new_unique();
        let mut account_account = Account::new(
            account_minimum_balance(),
            spl_token::state::Account::get_packed_len(),
            program_id,
        );
        let mut mint_authority_account = Account::default();
        let mut rent_sysvar_account = create_account_for_test(&Rent::free());

        do_process_instruction(
            initialize_account(program_id, &account_key, mint_key, account_owner_key).unwrap(),
            vec![
                &mut account_account,
                &mut mint_account,
                &mut mint_authority_account,
                &mut rent_sysvar_account,
            ],
        )
        .unwrap();

        if amount > 0 {
            do_process_instruction(
                mint_to(
                    program_id,
                    mint_key,
                    &account_key,
                    mint_authority_key,
                    &[],
                    amount,
                )
                .unwrap(),
                vec![
                    &mut mint_account,
                    &mut account_account,
                    &mut mint_authority_account,
                ],
            )
            .unwrap();
        }

        (account_key, account_account)
    }

    fn create_mint(
        program_id: &Pubkey,
        authority_key: &Pubkey,
        freeze_authority: Option<&Pubkey>,
    ) -> (Pubkey, Account) {
        let mint_key = Pubkey::new_unique();
        let mut mint_account = Account::new(
            mint_minimum_balance(),
            spl_token::state::Mint::get_packed_len(),
            program_id,
        );
        let mut rent_sysvar_account = create_account_for_test(&Rent::free());

        do_process_instruction(
            initialize_mint(program_id, &mint_key, authority_key, freeze_authority, 2).unwrap(),
            vec![&mut mint_account, &mut rent_sysvar_account],
        )
        .unwrap();

        (mint_key, mint_account)
    }

    #[test]
    fn test_token_program_id_error() {
        test_syscall_stubs();
        let swap_key = Pubkey::new_unique();
        let mut mint = (Pubkey::new_unique(), Account::default());
        let mut destination = (Pubkey::new_unique(), Account::default());
        let token_program = (spl_token::id(), Account::default());
        let (authority_key, nonce) =
            Pubkey::find_program_address(&[&swap_key.to_bytes()[..]], &SWAP_PROGRAM_ID);
        let mut authority = (authority_key, Account::default());
        let swap_bytes = swap_key.to_bytes();
        let authority_signature_seeds = [&swap_bytes[..32], &[nonce]];
        let signers = &[&authority_signature_seeds[..]];
        let ix = mint_to(
            &token_program.0,
            &mint.0,
            &destination.0,
            &authority.0,
            &[],
            10,
        )
        .unwrap();
        let mint = (&mut mint).into();
        let destination = (&mut destination).into();
        let authority = (&mut authority).into();

        let err = invoke_signed(&ix, &[mint, destination, authority], signers).unwrap_err();
        assert_eq!(err, ProgramError::InvalidAccountData);
    }

    #[test]
    fn test_initialize() {
        let user_key = Pubkey::new_unique();

        let token_amount = 1000;
        let tokenamount = 10;

        let mut accounts =
            SwapAccountInfo::new(&user_key, token_amount);

        // wrong nonce for authority_key
        {
            let old_nonce = accounts.nonce;
            accounts.nonce = old_nonce - 1;
            assert_eq!(
                Err(StreamError::InvalidProgramAddress.into()),
                accounts.initialize_swap()
            );
            accounts.nonce = old_nonce;
        }

        // uninitialized token a account
        {
            let old_account = accounts.token_account;
            accounts.token_account = Account::new(0, 0, &spl_token::id());
            assert_eq!(
                Err(StreamError::ExpectedAccount.into()),
                accounts.initialize_swap()
            );
            accounts.token_account = old_account;
        }

        // uninitialized pool mint
        {
            let old_account = accounts.stream_token_mint_account;
            accounts.stream_token_mint_account = Account::new(0, 0, &spl_token::id());
            assert_eq!(
                Err(StreamError::ExpectedMint.into()),
                accounts.initialize_swap()
            );
            accounts.stream_token_mint_account = old_account;
        }

        // token A account owner is not swap authority
        {
            let (_token_key, token_account) = mint_token(
                &spl_token::id(),
                &accounts.token_mint_key,
                &mut accounts.token_mint_account,
                &user_key,
                &user_key,
                0,
            );
            let old_account = accounts.token_account;
            accounts.token_account = token_account;
            assert_eq!(
                Err(StreamError::InvalidOwner.into()),
                accounts.initialize_swap()
            );
            accounts.token_account = old_account;
        }

        // pool token account owner is swap authority
        {
            let (_pool_token_key, pool_tokenccount) = mint_token(
                &spl_token::id(),
                &accounts.stream_token_mint_key,
                &mut accounts.stream_token_mint_account,
                &accounts.authority_key,
                &accounts.authority_key,
                0,
            );
            let old_account = accounts.pool_tokenccount;
            accounts.pool_tokenccount = pool_tokenccount;
            assert_eq!(
                Err(StreamError::InvalidOutputOwner.into()),
                accounts.initialize_swap()
            );
            accounts.pool_tokenccount = old_account;
        }

        // pool fee account owner is swap authority
        {
            let (_pool_fee_key, stream_fee_account) = mint_token(
                &spl_token::id(),
                &accounts.stream_token_mint_key,
                &mut accounts.stream_token_mint_account,
                &accounts.authority_key,
                &accounts.authority_key,
                0,
            );
            let old_account = accounts.stream_fee_account;
            accounts.stream_fee_account = stream_fee_account;
            assert_eq!(
                Err(StreamError::InvalidOutputOwner.into()),
                accounts.initialize_swap()
            );
            accounts.stream_fee_account = old_account;
        }

        // pool mint authority is not swap authority
        {
            let (_stream_token_mint_key, stream_token_mint_account) =
                create_mint(&spl_token::id(), &user_key, None);
            let old_mint = accounts.stream_token_mint_account;
            accounts.stream_token_mint_account = stream_token_mint_account;
            assert_eq!(
                Err(StreamError::InvalidOwner.into()),
                accounts.initialize_swap()
            );
            accounts.stream_token_mint_account = old_mint;
        }

        // pool mint token has freeze authority
        {
            let (_stream_token_mint_key, stream_token_mint_account) =
                create_mint(&spl_token::id(), &accounts.authority_key, Some(&user_key));
            let old_mint = accounts.stream_token_mint_account;
            accounts.stream_token_mint_account = stream_token_mint_account;
            assert_eq!(
                Err(StreamError::InvalidFreezeAuthority.into()),
                accounts.initialize_swap()
            );
            accounts.stream_token_mint_account = old_mint;
        }

        // token A account owned by wrong program
        {
            let (_token_key, mut token_account) = mint_token(
                &spl_token::id(),
                &accounts.token_mint_key,
                &mut accounts.token_mint_account,
                &user_key,
                &accounts.authority_key,
                token_amount,
            );
            token_account.owner = SWAP_PROGRAM_ID;
            let old_account = accounts.token_account;
            accounts.token_account = token_account;
            assert_eq!(
                Err(StreamError::IncorrectTokenProgramId.into()),
                accounts.initialize_swap()
            );
            accounts.token_account = old_account;
        }

        // empty token A account
        {
            let (_token_key, token_account) = mint_token(
                &spl_token::id(),
                &accounts.token_mint_key,
                &mut accounts.token_mint_account,
                &user_key,
                &accounts.authority_key,
                0,
            );
            let old_account = accounts.token_account;
            accounts.token_account = token_account;
            assert_eq!(
                Err(StreamError::EmptySupply.into()),
                accounts.initialize_swap()
            );
            accounts.token_account = old_account;
        }

        // invalid pool tokens
        {
            let old_mint = accounts.stream_token_mint_account;
            let old_pool_account = accounts.pool_tokenccount;

            let (_stream_token_mint_key, stream_token_mint_account) =
                create_mint(&spl_token::id(), &accounts.authority_key, None);
            accounts.stream_token_mint_account = stream_token_mint_account;

            let (_empty_pool_token_key, empty_pool_tokenccount) = mint_token(
                &spl_token::id(),
                &accounts.stream_token_mint_key,
                &mut accounts.stream_token_mint_account,
                &accounts.authority_key,
                &user_key,
                0,
            );

            let (_pool_token_key, pool_tokenccount) = mint_token(
                &spl_token::id(),
                &accounts.stream_token_mint_key,
                &mut accounts.stream_token_mint_account,
                &accounts.authority_key,
                &user_key,
                tokenamount,
            );

            // non-empty pool token account
            accounts.pool_tokenccount = pool_tokenccount;
            assert_eq!(
                Err(StreamError::InvalidSupply.into()),
                accounts.initialize_swap()
            );

            // pool tokens already in circulation
            accounts.pool_tokenccount = empty_pool_tokenccount;
            assert_eq!(
                Err(StreamError::InvalidSupply.into()),
                accounts.initialize_swap()
            );

            accounts.stream_token_mint_account = old_mint;
            accounts.pool_tokenccount = old_pool_account;
        }

        // pool fee account has wrong mint
        {
            let (_pool_fee_key, stream_fee_account) = mint_token(
                &spl_token::id(),
                &accounts.token_mint_key,
                &mut accounts.token_mint_account,
                &user_key,
                &user_key,
                0,
            );
            let old_account = accounts.stream_fee_account;
            accounts.stream_fee_account = stream_fee_account;
            assert_eq!(
                Err(StreamError::IncorrectPoolMint.into()),
                accounts.initialize_swap()
            );
            accounts.stream_fee_account = old_account;
        }

        // token A account is delegated
        {
            do_process_instruction(
                approve(
                    &spl_token::id(),
                    &accounts.token_key,
                    &user_key,
                    &accounts.authority_key,
                    &[],
                    1,
                )
                .unwrap(),
                vec![
                    &mut accounts.token_account,
                    &mut Account::default(),
                    &mut Account::default(),
                ],
            )
            .unwrap();
            assert_eq!(
                Err(StreamError::InvalidDelegate.into()),
                accounts.initialize_swap()
            );

            do_process_instruction(
                revoke(
                    &spl_token::id(),
                    &accounts.token_key,
                    &accounts.authority_key,
                    &[],
                )
                .unwrap(),
                vec![&mut accounts.token_account, &mut Account::default()],
            )
            .unwrap();
        }


        // token A account has close authority
        {
            do_process_instruction(
                set_authority(
                    &spl_token::id(),
                    &accounts.token_key,
                    Some(&user_key),
                    AuthorityType::CloseAccount,
                    &accounts.authority_key,
                    &[],
                )
                .unwrap(),
                vec![&mut accounts.token_account, &mut Account::default()],
            )
            .unwrap();
            assert_eq!(
                Err(StreamError::InvalidCloseAuthority.into()),
                accounts.initialize_swap()
            );

            do_process_instruction(
                set_authority(
                    &spl_token::id(),
                    &accounts.token_key,
                    None,
                    AuthorityType::CloseAccount,
                    &user_key,
                    &[],
                )
                .unwrap(),
                vec![&mut accounts.token_account, &mut Account::default()],
            )
            .unwrap();
        }


        // wrong token program id
        {
            let wrong_program_id = Pubkey::new_unique();
            assert_eq!(
                Err(StreamError::IncorrectTokenProgramId.into()),
                do_process_instruction(
                    initialize(
                        &SWAP_PROGRAM_ID,
                        &wrong_program_id,
                        &accounts.swap_key,
                        &accounts.authority_key,
                        &accounts.token_key,
                        &accounts.stream_token_mint_key,
                        &accounts.pool_fee_key,
                        &accounts.pool_token_key,
                        accounts.nonce
                    )
                    .unwrap(),
                    vec![
                        &mut accounts.swap_account,
                        &mut Account::default(),
                        &mut accounts.token_account,
                        &mut accounts.stream_token_mint_account,
                        &mut accounts.stream_fee_account,
                        &mut accounts.pool_tokenccount,
                        &mut Account::default(),
                    ],
                )
            );
        }


        // create valid swap
        accounts.initialize_swap().unwrap();

        // create valid flat swap
        {
            
            let mut accounts =
                SwapAccountInfo::new(&user_key, token_amount);
            accounts.initialize_swap().unwrap();
        }

        // create again
        {
            assert_eq!(
                Err(StreamError::AlreadyInUse.into()),
                accounts.initialize_swap()
            );
        }
        let swap_state = StreamVersion::unpack(&accounts.swap_account.data).unwrap();
        assert!(swap_state.is_initialized());
        assert_eq!(swap_state.nonce(), accounts.nonce);
        assert_eq!(*swap_state.token_account(), accounts.token_key);
        assert_eq!(*swap_state.stream_token_mint(), accounts.stream_token_mint_key);
        assert_eq!(*swap_state.token_mint(), accounts.token_mint_key);
        assert_eq!(*swap_state.stream_fee_account(), accounts.pool_fee_key);
        let token = spl_token::state::Account::unpack(&accounts.token_account.data).unwrap();
        assert_eq!(token.amount, token_amount);

        let pool_account =
            spl_token::state::Account::unpack(&accounts.pool_tokenccount.data).unwrap();
        let stream_token_mint = spl_token::state::Mint::unpack(&accounts.stream_token_mint_account.data).unwrap();
        assert_eq!(stream_token_mint.supply, pool_account.amount);
    }

    #[test]
    fn test_deposit() {
        let user_key = Pubkey::new_unique();
        let depositor_key = Pubkey::new_unique();

        let token_amount = 1000;

        let mut accounts =
            SwapAccountInfo::new(&user_key, token_amount);

        // depositing 10% of the current pool amount in token A and B means
        // that our pool tokens will be worth 1 / 10 of the current pool amount
        let pool_amount = token_amount;

        // swap not initialized
        {
            let (
                token_key,
                mut token_account,
                pool_key,
                mut pool_account,
            ) = accounts.setup_tokenccounts(&user_key, &depositor_key, pool_amount, 0);
            assert_eq!(
                Err(ProgramError::UninitializedAccount),
                accounts.deposit_token(
                    &depositor_key,
                    &token_key,
                    &mut token_account,
                    &pool_key,
                    &mut pool_account,
                    pool_amount.try_into().unwrap(),
                )
            );
        }

        accounts.initialize_swap().unwrap();
    
    //     // wrong owner for swap account
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         let old_swap_account = accounts.swap_account;
    //         let mut wrong_swap_account = old_swap_account.clone();
    //         wrong_swap_account.owner = spl_token::id();
    //         accounts.swap_account = wrong_swap_account;
    //         assert_eq!(
    //             Err(ProgramError::IncorrectProgramId),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //         accounts.swap_account = old_swap_account;
    //     }

    //     // wrong nonce for authority_key
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         let old_authority = accounts.authority_key;
    //         let (bad_authority_key, _nonce) = Pubkey::find_program_address(
    //             &[&accounts.swap_key.to_bytes()[..]],
    //             &spl_token::id(),
    //         );
    //         accounts.authority_key = bad_authority_key;
    //         assert_eq!(
    //             Err(StreamError::InvalidProgramAddress.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //         accounts.authority_key = old_authority;
    //     }

    //     // not enough token A
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &depositor_key,
    //             deposit_a / 2,
    //             deposit_b,
    //             0,
    //         );
    //         assert_eq!(
    //             Err(TokenError::InsufficientFunds.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //     }

    //     // not enough token B
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &depositor_key,
    //             deposit_a,
    //             deposit_b / 2,
    //             0,
    //         );
    //         assert_eq!(
    //             Err(TokenError::InsufficientFunds.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //     }

    //     // wrong swap token accounts
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         assert_eq!(
    //             Err(TokenError::MintMismatch.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //     }

    //     // wrong pool token account
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             _pool_key,
    //             mut _pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         let (
    //             wrong_token_key,
    //             mut wrong_tokenccount,
    //             _token_b_key,
    //             mut _token_b_account,
    //             _pool_key,
    //             mut _pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         assert_eq!(
    //             Err(TokenError::MintMismatch.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &wrong_token_key,
    //                 &mut wrong_tokenccount,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //     }

    //     // no approval
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         let user_transfer_authority_key = Pubkey::new_unique();
    //         assert_eq!(
    //             Err(TokenError::OwnerMismatch.into()),
    //             do_process_instruction(
    //                 deposit_token(
    //                     &SWAP_PROGRAM_ID,
    //                     &spl_token::id(),
    //                     &accounts.swap_key,
    //                     &accounts.authority_key,
    //                     &user_transfer_authority_key,
    //                     &token_key,
    //                     &token_b_key,
    //                     &accounts.token_key,
    //                     &accounts.token_b_key,
    //                     &accounts.stream_token_mint_key,
    //                     &pool_key,
    //                     DepositToken {
    //                         tokenamount: pool_amount.try_into().unwrap(),
    //                         maximum_token_amount: deposit_a,
    //                         maximum_token_b_amount: deposit_b,
    //                     },
    //                 )
    //                 .unwrap(),
    //                 vec![
    //                     &mut accounts.swap_account,
    //                     &mut Account::default(),
    //                     &mut Account::default(),
    //                     &mut token_account,
    //                     &mut token_b_account,
    //                     &mut accounts.token_account,
    //                     &mut accounts.token_b_account,
    //                     &mut accounts.stream_token_mint_account,
    //                     &mut pool_account,
    //                     &mut Account::default(),
    //                 ],
    //             )
    //         );
    //     }

    //     // wrong token program id
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         let wrong_key = Pubkey::new_unique();
    //         assert_eq!(
    //             Err(StreamError::IncorrectTokenProgramId.into()),
    //             do_process_instruction(
    //                 deposit_token(
    //                     &SWAP_PROGRAM_ID,
    //                     &wrong_key,
    //                     &accounts.swap_key,
    //                     &accounts.authority_key,
    //                     &accounts.authority_key,
    //                     &token_key,
    //                     &token_b_key,
    //                     &accounts.token_key,
    //                     &accounts.token_b_key,
    //                     &accounts.stream_token_mint_key,
    //                     &pool_key,
    //                     DepositToken {
    //                         tokenamount: pool_amount.try_into().unwrap(),
    //                         maximum_token_amount: deposit_a,
    //                         maximum_token_b_amount: deposit_b,
    //                     },
    //                 )
    //                 .unwrap(),
    //                 vec![
    //                     &mut accounts.swap_account,
    //                     &mut Account::default(),
    //                     &mut Account::default(),
    //                     &mut token_account,
    //                     &mut token_b_account,
    //                     &mut accounts.token_account,
    //                     &mut accounts.token_b_account,
    //                     &mut accounts.stream_token_mint_account,
    //                     &mut pool_account,
    //                     &mut Account::default(),
    //                 ],
    //             )
    //         );
    //     }

    //     // wrong swap token accounts
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);

    //         let old_a_key = accounts.token_key;
    //         let old_a_account = accounts.token_account;

    //         accounts.token_key = token_key;
    //         accounts.token_account = token_account.clone();

    //         // wrong swap token a account
    //         assert_eq!(
    //             Err(StreamError::IncorrectSwapAccount.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );

    //         accounts.token_key = old_a_key;
    //         accounts.token_account = old_a_account;

    //         let old_b_key = accounts.token_b_key;
    //         let old_b_account = accounts.token_b_account;

    //         accounts.token_b_key = token_b_key;
    //         accounts.token_b_account = token_b_account.clone();

    //         // wrong swap token b account
    //         assert_eq!(
    //             Err(StreamError::IncorrectSwapAccount.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );

    //         accounts.token_b_key = old_b_key;
    //         accounts.token_b_account = old_b_account;
    //     }

    //     // wrong mint
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         let (stream_token_mint_key, stream_token_mint_account) =
    //             create_mint(&spl_token::id(), &accounts.authority_key, None);
    //         let old_pool_key = accounts.stream_token_mint_key;
    //         let old_pool_account = accounts.stream_token_mint_account;
    //         accounts.stream_token_mint_key = stream_token_mint_key;
    //         accounts.stream_token_mint_account = stream_token_mint_account;

    //         assert_eq!(
    //             Err(StreamError::IncorrectPoolMint.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );

    //         accounts.stream_token_mint_key = old_pool_key;
    //         accounts.stream_token_mint_account = old_pool_account;
    //     }

    //     // deposit 1 pool token fails beacuse it equates to 0 swap tokens
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         assert_eq!(
    //             Err(StreamError::ZeroTradingTokens.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 1,
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //     }

    //     // slippage exceeded
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         // maximum A amount in too low
    //         assert_eq!(
    //             Err(StreamError::ExceededSlippage.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a / 10,
    //                 deposit_b,
    //             )
    //         );
    //         // maximum B amount in too low
    //         assert_eq!(
    //             Err(StreamError::ExceededSlippage.into()),
    //             accounts.deposit_token(
    //                 &depositor_key,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b / 10,
    //             )
    //         );
    //     }

    //     // invalid input: can't use swap pool tokens as source
    //     {
    //         let (
    //             _token_key,
    //             _token_account,
    //             _token_b_key,
    //             _token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &depositor_key, deposit_a, deposit_b, 0);
    //         let swap_token_key = accounts.token_key;
    //         let mut swap_token_account = accounts.get_tokenccount(&swap_token_key).clone();
    //         let swap_token_b_key = accounts.token_b_key;
    //         let mut swap_token_b_account = accounts.get_tokenccount(&swap_token_b_key).clone();
    //         let authority_key = accounts.authority_key;
    //         assert_eq!(
    //             Err(StreamError::InvalidInput.into()),
    //             accounts.deposit_token(
    //                 &authority_key,
    //                 &swap_token_key,
    //                 &mut swap_token_account,
    //                 &swap_token_b_key,
    //                 &mut swap_token_b_account,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 pool_amount.try_into().unwrap(),
    //                 deposit_a,
    //                 deposit_b,
    //             )
    //         );
    //     }

        // correctly deposit
        {
            let (
                token_key,
                mut token_account,
                pool_key,
                mut pool_account,
            ) = accounts.setup_tokenccounts(&user_key, &depositor_key, pool_amount, 0);
            accounts
                .deposit_token(
                    &depositor_key,
                    &token_key,
                    &mut token_account,
                    &pool_key,
                    &mut pool_account,
                    pool_amount.try_into().unwrap(),
                )
                .unwrap();

            let swap_token =
                spl_token::state::Account::unpack(&accounts.token_account.data).unwrap();
            assert_eq!(swap_token.amount, pool_amount + token_amount);

            let token = spl_token::state::Account::unpack(&token_account.data).unwrap();
            assert_eq!(token.amount, 0);
            let pool_account = spl_token::state::Account::unpack(&pool_account.data).unwrap();
            let swap_pool_account =
                spl_token::state::Account::unpack(&accounts.pool_tokenccount.data).unwrap();
            let stream_token_mint =
                spl_token::state::Mint::unpack(&accounts.stream_token_mint_account.data).unwrap();
            assert_eq!(
                stream_token_mint.supply,
                pool_account.amount + swap_pool_account.amount
            );
        }
    }


    #[test]
    fn test_withdraw() {
        let user_key = Pubkey::new_unique();

        let withdrawer_key = Pubkey::new_unique();
        let initial_a = 100;
        let initial_pool =  1000;
        let withdraw_amount = 50;



        let mut accounts =
            SwapAccountInfo::new(&user_key, initial_a);

        // swap not initialized
        {
            let (
                token_key,
                mut token_account,
                pool_key,
                mut pool_account,
            ) = accounts.setup_tokenccounts(&user_key, &withdrawer_key, withdraw_amount, 0);
            assert_eq!(
                Err(ProgramError::UninitializedAccount),
                accounts.withdraw_token(
                    &withdrawer_key,
                    &pool_key,
                    &mut pool_account,
                    &token_key,
                    &mut token_account,
                    withdraw_amount.try_into().unwrap(),
                )
            );
        }

        accounts.initialize_swap().unwrap();
    
    //     // wrong owner for swap account
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &withdrawer_key, initial_a, initial_b, 0);
    //         let old_swap_account = accounts.swap_account;
    //         let mut wrong_swap_account = old_swap_account.clone();
    //         wrong_swap_account.owner = spl_token::id();
    //         accounts.swap_account = wrong_swap_account;
    //         assert_eq!(
    //             Err(ProgramError::IncorrectProgramId),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );
    //         accounts.swap_account = old_swap_account;
    //     }

    //     // wrong nonce for authority_key
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &withdrawer_key, initial_a, initial_b, 0);
    //         let old_authority = accounts.authority_key;
    //         let (bad_authority_key, _nonce) = Pubkey::find_program_address(
    //             &[&accounts.swap_key.to_bytes()[..]],
    //             &spl_token::id(),
    //         );
    //         accounts.authority_key = bad_authority_key;
    //         assert_eq!(
    //             Err(StreamError::InvalidProgramAddress.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );
    //         accounts.authority_key = old_authority;
    //     }

    //     // not enough pool tokens
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             to_u64(withdraw_amount).unwrap() / 2u64,
    //         );
    //         assert_eq!(
    //             Err(TokenError::InsufficientFunds.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount / 2,
    //                 minimum_token_b_amount / 2,
    //             )
    //         );
    //     }

    //     // wrong token a / b accounts
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             withdraw_amount.try_into().unwrap(),
    //         );
    //         assert_eq!(
    //             Err(TokenError::MintMismatch.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );
    //     }

    //     // wrong pool token account
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             _pool_key,
    //             _pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             withdraw_amount.try_into().unwrap(),
    //         );
    //         let (
    //             wrong_token_key,
    //             mut wrong_token_account,
    //             _token_b_key,
    //             _token_b_account,
    //             _pool_key,
    //             _pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             withdraw_amount.try_into().unwrap(),
    //             initial_b,
    //             withdraw_amount.try_into().unwrap(),
    //         );
    //         assert_eq!(
    //             Err(TokenError::MintMismatch.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &wrong_token_key,
    //                 &mut wrong_token_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );
    //     }

    //     // wrong pool fee account
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             wrong_pool_key,
    //             wrong_pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             withdraw_amount.try_into().unwrap(),
    //         );
    //         let (
    //             _token_key,
    //             _token_account,
    //             _token_b_key,
    //             _token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             withdraw_amount.try_into().unwrap(),
    //         );
    //         let old_stream_fee_account = accounts.stream_fee_account;
    //         let old_pool_fee_key = accounts.pool_fee_key;
    //         accounts.stream_fee_account = wrong_pool_account;
    //         accounts.pool_fee_key = wrong_pool_key;
    //         assert_eq!(
    //             Err(StreamError::IncorrectFeeAccount.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             ),
    //         );
    //         accounts.stream_fee_account = old_stream_fee_account;
    //         accounts.pool_fee_key = old_pool_fee_key;
    //     }

    //     // no approval
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             0,
    //             0,
    //             withdraw_amount.try_into().unwrap(),
    //         );
    //         let user_transfer_authority_key = Pubkey::new_unique();
    //         assert_eq!(
    //             Err(TokenError::OwnerMismatch.into()),
    //             do_process_instruction(
    //                 withdraw_token(
    //                     &SWAP_PROGRAM_ID,
    //                     &spl_token::id(),
    //                     &accounts.swap_key,
    //                     &accounts.authority_key,
    //                     &user_transfer_authority_key,
    //                     &accounts.stream_token_mint_key,
    //                     &accounts.pool_fee_key,
    //                     &pool_key,
    //                     &accounts.token_key,
    //                     &accounts.token_b_key,
    //                     &token_key,
    //                     &token_b_key,
    //                     WithdrawToken {
    //                         tokenamount: withdraw_amount.try_into().unwrap(),
    //                         minimum_token_amount,
    //                         minimum_token_b_amount,
    //                     }
    //                 )
    //                 .unwrap(),
    //                 vec![
    //                     &mut accounts.swap_account,
    //                     &mut Account::default(),
    //                     &mut Account::default(),
    //                     &mut accounts.stream_token_mint_account,
    //                     &mut pool_account,
    //                     &mut accounts.token_account,
    //                     &mut accounts.token_b_account,
    //                     &mut token_account,
    //                     &mut token_b_account,
    //                     &mut accounts.stream_fee_account,
    //                     &mut Account::default(),
    //                 ],
    //             )
    //         );
    //     }

    //     // wrong token program id
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             withdraw_amount.try_into().unwrap(),
    //         );
    //         let wrong_key = Pubkey::new_unique();
    //         assert_eq!(
    //             Err(StreamError::IncorrectTokenProgramId.into()),
    //             do_process_instruction(
    //                 withdraw_token(
    //                     &SWAP_PROGRAM_ID,
    //                     &wrong_key,
    //                     &accounts.swap_key,
    //                     &accounts.authority_key,
    //                     &accounts.authority_key,
    //                     &accounts.stream_token_mint_key,
    //                     &accounts.pool_fee_key,
    //                     &pool_key,
    //                     &accounts.token_key,
    //                     &accounts.token_b_key,
    //                     &token_key,
    //                     &token_b_key,
    //                     WithdrawToken {
    //                         tokenamount: withdraw_amount.try_into().unwrap(),
    //                         minimum_token_amount,
    //                         minimum_token_b_amount,
    //                     },
    //                 )
    //                 .unwrap(),
    //                 vec![
    //                     &mut accounts.swap_account,
    //                     &mut Account::default(),
    //                     &mut Account::default(),
    //                     &mut accounts.stream_token_mint_account,
    //                     &mut pool_account,
    //                     &mut accounts.token_account,
    //                     &mut accounts.token_b_account,
    //                     &mut token_account,
    //                     &mut token_b_account,
    //                     &mut accounts.stream_fee_account,
    //                     &mut Account::default(),
    //                 ],
    //             )
    //         );
    //     }

    //     // wrong swap token accounts
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             initial_pool.try_into().unwrap(),
    //         );

    //         let old_a_key = accounts.token_key;
    //         let old_a_account = accounts.token_account;

    //         accounts.token_key = token_key;
    //         accounts.token_account = token_account.clone();

    //         // wrong swap token a account
    //         assert_eq!(
    //             Err(StreamError::IncorrectSwapAccount.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );

    //         accounts.token_key = old_a_key;
    //         accounts.token_account = old_a_account;

    //         let old_b_key = accounts.token_b_key;
    //         let old_b_account = accounts.token_b_account;

    //         accounts.token_b_key = token_b_key;
    //         accounts.token_b_account = token_b_account.clone();

    //         // wrong swap token b account
    //         assert_eq!(
    //             Err(StreamError::IncorrectSwapAccount.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );

    //         accounts.token_b_key = old_b_key;
    //         accounts.token_b_account = old_b_account;
    //     }

    //     // wrong mint
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             initial_pool.try_into().unwrap(),
    //         );
    //         let (stream_token_mint_key, stream_token_mint_account) =
    //             create_mint(&spl_token::id(), &accounts.authority_key, None);
    //         let old_pool_key = accounts.stream_token_mint_key;
    //         let old_pool_account = accounts.stream_token_mint_account;
    //         accounts.stream_token_mint_key = stream_token_mint_key;
    //         accounts.stream_token_mint_account = stream_token_mint_account;

    //         assert_eq!(
    //             Err(StreamError::IncorrectPoolMint.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );

    //         accounts.stream_token_mint_key = old_pool_key;
    //         accounts.stream_token_mint_account = old_pool_account;
    //     }

    //     // withdrawing 1 pool token fails because it equates to 0 output tokens
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             initial_pool.try_into().unwrap(),
    //         );
    //         assert_eq!(
    //             Err(StreamError::ZeroTradingTokens.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 1,
    //                 0,
    //                 0,
    //             )
    //         );
    //     }

    //     // slippage exceeded
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             initial_pool.try_into().unwrap(),
    //         );
    //         // minimum A amount out too high
    //         assert_eq!(
    //             Err(StreamError::ExceededSlippage.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount * 10,
    //                 minimum_token_b_amount,
    //             )
    //         );
    //         // minimum B amount out too high
    //         assert_eq!(
    //             Err(StreamError::ExceededSlippage.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount * 10,
    //             )
    //         );
    //     }

    //     // invalid input: can't use swap pool tokens as destination
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             token_b_key,
    //             mut token_b_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &withdrawer_key,
    //             initial_a,
    //             initial_b,
    //             initial_pool.try_into().unwrap(),
    //         );
    //         let swap_token_key = accounts.token_key;
    //         let mut swap_token_account = accounts.get_tokenccount(&swap_token_key).clone();
    //         assert_eq!(
    //             Err(StreamError::InvalidInput.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &swap_token_key,
    //                 &mut swap_token_account,
    //                 &token_b_key,
    //                 &mut token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );
    //         let swap_token_b_key = accounts.token_b_key;
    //         let mut swap_token_b_account = accounts.get_tokenccount(&swap_token_b_key).clone();
    //         assert_eq!(
    //             Err(StreamError::InvalidInput.into()),
    //             accounts.withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 &swap_token_b_key,
    //                 &mut swap_token_b_account,
    //                 withdraw_amount.try_into().unwrap(),
    //                 minimum_token_amount,
    //                 minimum_token_b_amount,
    //             )
    //         );
    //     }

        // correct withdrawal
        {
            let (
                token_key,
                mut token_account,
                pool_key,
                mut pool_account,
            ) = accounts.setup_tokenccounts(
                &user_key,
                &withdrawer_key,
                initial_a,
                initial_pool.try_into().unwrap(),
            );

            accounts
                .withdraw_token(
                    &withdrawer_key,
                    &pool_key,
                    &mut pool_account,
                    &token_key,
                    &mut token_account,
                    withdraw_amount.try_into().unwrap(),
                )
                .unwrap();

            let token =
                spl_token::state::Account::unpack(&accounts.token_account.data).unwrap();

            let stream_token_mint =
                spl_token::state::Mint::unpack(&accounts.stream_token_mint_account.data).unwrap();

            assert_eq!(
                token.amount,
                withdraw_amount
            );

            let token = spl_token::state::Account::unpack(&token_account.data).unwrap();
            assert_eq!(
                token.amount,
                initial_a + withdraw_amount
            );

            let pool_account = spl_token::state::Account::unpack(&pool_account.data).unwrap();
            assert_eq!(
                pool_account.amount,
                initial_pool - withdraw_amount
            );
        }
    }
        // correct withdrawal from fee account
    //     {
    //         let (
    //             token_key,
    //             mut token_account,
    //             _pool_key,
    //             mut _pool_account,
    //         ) = accounts.setup_tokenccounts(&user_key, &withdrawer_key, 0, token_amount);

    //         let pool_fee_key = accounts.pool_fee_key;
    //         let mut stream_fee_account = accounts.stream_fee_account.clone();
    //         let fee_account = spl_token::state::Account::unpack(&stream_fee_account.data).unwrap();
    //         let pool_fee_amount = fee_account.amount;

    //         accounts
    //             .withdraw_token(
    //                 &user_key,
    //                 &pool_fee_key,
    //                 &mut stream_fee_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 token_amount,
    //             )
    //             .unwrap();

    //         let swap_token =
    //             spl_token::state::Account::unpack(&accounts.token_account.data).unwrap();
    //         let stream_token_mint =
    //             spl_token::state::Mint::unpack(&accounts.stream_token_mint_account.data).unwrap();

    //         let token = spl_token::state::Account::unpack(&token_account.data).unwrap();
    //         assert_eq!(
    //             token.amount,
    //             TryInto::<u64>::try_into(token_amount).unwrap()
    //         );
    //     }
    // }
}
