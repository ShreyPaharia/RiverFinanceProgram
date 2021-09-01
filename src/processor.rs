//! Program state processor

use crate::constraints::{Constraints, SWAP_CONSTRAINTS};
use crate::{
    error::StreamTokenError,
    instruction::{
        DepositToken, Initialize,
        SwapInstruction, WithdrawToken,
        StartStream,StopStream
    },
    state::{StreamState, StreamV1, StreamVersion, 
        UserStreamInfo, BilateralStreamAgreement, UserStreamBalance,
        AddBilateralStreamParams, RemoveBilateralStreamParams, StreamAgreement},
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
    sysvar::{clock::Clock, fees::Fees, rent::Rent, Sysvar},

};
use std::convert::TryInto;

/// Program state handler.
pub struct Processor {}
impl Processor {
    /// Unpacks a spl_token `Account`.
    pub fn unpack_tokenccount(
        account_info: &AccountInfo,
        token_program_id: &Pubkey,
    ) -> Result<spl_token::state::Account, StreamTokenError> {
        if account_info.owner != token_program_id {
            Err(StreamTokenError::IncorrectTokenProgramId)
        } else {
            spl_token::state::Account::unpack(&account_info.data.borrow())
                .map_err(|_| StreamTokenError::ExpectedAccount)
        }
    }

    /// Unpacks a spl_token `Mint`.
    pub fn unpack_mint(
        account_info: &AccountInfo,
        token_program_id: &Pubkey,
    ) -> Result<spl_token::state::Mint, StreamTokenError> {
        if account_info.owner != token_program_id {
            Err(StreamTokenError::IncorrectTokenProgramId)
        } else {
            spl_token::state::Mint::unpack(&account_info.data.borrow())
                .map_err(|_| StreamTokenError::ExpectedMint)
        }
    }

    /// Calculates the authority id by generating a program address.
    pub fn authority_id(
        program_id: &Pubkey,
        my_info: &Pubkey,
        nonce: u8,
    ) -> Result<Pubkey, StreamTokenError> {
        Pubkey::create_program_address(&[&my_info.to_bytes()[..32], &[nonce]], program_id)
            .or(Err(StreamTokenError::InvalidProgramAddress))
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
            return Err(StreamTokenError::InvalidProgramAddress.into());
        }
        if *token_info.key != *token_swap.token_account() {
            return Err(StreamTokenError::IncorrectSwapAccount.into());
        }
        if *stream_token_mint_info.key != *token_swap.stream_token_mint() {
            return Err(StreamTokenError::IncorrectPoolMint.into());
        }
        if *token_program_info.key != *token_swap.token_program_id() {
            return Err(StreamTokenError::IncorrectTokenProgramId.into());
        }
        if let Some(user_token_info) = user_token_info {
            if token_info.key == user_token_info.key {
                return Err(StreamTokenError::InvalidInput.into());
            }
        }
        if let Some(stream_fee_account_info) = stream_fee_account_info {
            if *stream_fee_account_info.key != *token_swap.stream_fee_account() {
                return Err(StreamTokenError::IncorrectFeeAccount.into());
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
            return Err(StreamTokenError::AlreadyInUse.into());
        }

        if *authority_info.key != Self::authority_id(program_id, swap_info.key, nonce)? {
            return Err(StreamTokenError::InvalidProgramAddress.into());
        }
        let token = Self::unpack_tokenccount(token_info, &token_program_id)?;
        let fee_account = Self::unpack_tokenccount(fee_account_info, &token_program_id)?;
        let destination = Self::unpack_tokenccount(destination_info, &token_program_id)?;
        let stream_token_mint = Self::unpack_mint(stream_token_mint_info, &token_program_id)?;
        if *authority_info.key != token.owner {
            return Err(StreamTokenError::InvalidOwner.into());
        }
        if *authority_info.key == destination.owner {
            return Err(StreamTokenError::InvalidOutputOwner.into());
        }
        if *authority_info.key == fee_account.owner {
            return Err(StreamTokenError::InvalidOutputOwner.into());
        }
        if COption::Some(*authority_info.key) != stream_token_mint.mint_authority {
            return Err(StreamTokenError::InvalidOwner.into());
        }

        if token.amount == 0 {
            return Err(StreamTokenError::EmptySupply.into());
        }
      
        if token.delegate.is_some() {
            return Err(StreamTokenError::InvalidDelegate.into());
        }

        if token.close_authority.is_some() {
            return Err(StreamTokenError::InvalidCloseAuthority.into());
        }

        if stream_token_mint.supply != 0 {
            return Err(StreamTokenError::InvalidSupply.into());
        }
        if stream_token_mint.freeze_authority.is_some() {
            return Err(StreamTokenError::InvalidFreezeAuthority.into());
        }
        if *stream_token_mint_info.key != fee_account.mint {
            return Err(StreamTokenError::IncorrectPoolMint.into());
        }

        if let Some(swap_constraints) = swap_constraints {
            let owner_key = swap_constraints
                .owner_key
                .parse::<Pubkey>()
                .map_err(|_| StreamTokenError::InvalidOwner)?;
            if fee_account.owner != owner_key {
                return Err(StreamTokenError::InvalidOwner.into());
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
            return Err(StreamTokenError::InsufficientFunds.into());
        }
        if token_amount == 0 {
            return Err(StreamTokenError::ZeroTradingTokens.into());
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
            //     .ok_or(StreamTokenError::FeeCalculationFailure)?
        };
        let tokenamount = to_u128(tokenamount)?
            .checked_sub(withdraw_fee)
            .ok_or(StreamTokenError::CalculationFailure)?;

        let token_amount = token.amount;

        if token_amount == 0 && token.amount != 0 {
            return Err(StreamTokenError::ZeroTradingTokens.into());
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
            flow_rate: u64,
            accounts: &[AccountInfo],
        ) -> ProgramResult {
            let account_info_iter = &mut accounts.iter();
            let stream_token_info = next_account_info(account_info_iter)?;
            let authority_info = next_account_info(account_info_iter)?;
            let user_transfer_authority_info = next_account_info(account_info_iter)?;
            let user_stream_token_account = next_account_info(account_info_iter)?;
            let user_stream_agreements_account = next_account_info(account_info_iter)?;
            let receiver_stream_token_account = next_account_info(account_info_iter)?;
            let receiver_stream_agreements_account = next_account_info(account_info_iter)?;
            let token_program_info = next_account_info(account_info_iter)?;
    
            let stream_token_data = StreamVersion::unpack(&stream_token_info.data.borrow())?;
    
            // Self::check_accounts(
            //     stream_token_data.as_ref(),
            //     program_id,
            //     stream_token_info,
            //     authority_info,
            //     token_info,
            //     stream_token_mint_info,
            //     token_program_info,
            //     Some(source_a_info),
            //     None,
            // )?;
    
            let stream_token = Self::unpack_tokenccount(user_stream_token_account, stream_token_data.token_program_id())?;

            let stream_token_amount = stream_token.amount;

            let threshold_amount = 0u64;
            if stream_token_amount < threshold_amount {
                return Err(StreamTokenError::InsufficientFunds.into());
            }
            if stream_token_amount == 0 {
                return Err(StreamTokenError::ZeroTradingTokens.into());
            }

            let now = Clock::get()?.unix_timestamp as u64;
            let mut user_stream_info = UserStreamInfo::unpack(&user_stream_agreements_account.data.borrow())?;
            let mut receiver_stream_info = UserStreamInfo::unpack(&receiver_stream_agreements_account.data.borrow())?;

            if !user_stream_info.is_initialized {
                user_stream_info = UserStreamInfo::new(*stream_token_info.key)
            }
            let agreementInfo = BilateralStreamAgreement {
                flow_rate: flow_rate,
                sender: *user_stream_token_account.key,
                receiver: *receiver_stream_token_account.key,
            };

            let mut add_stream_params_user = AddBilateralStreamParams{
                user_stream_info: user_stream_info,
                sender: *user_stream_token_account.key,
                receiver: *receiver_stream_token_account.key,
                is_user_sender: true,
                flow_rate: flow_rate,
                now:now,
            };

            let mut add_stream_params_receiver = AddBilateralStreamParams{
                user_stream_info: receiver_stream_info,
                sender: *user_stream_token_account.key,
                receiver: *receiver_stream_token_account.key,
                is_user_sender: false,
                flow_rate: flow_rate,
                now:now,
            };

            let user_stream_info_updated = agreementInfo.add_stream(add_stream_params_user)?;
            let receiver_stream_info_updated = agreementInfo.add_stream(add_stream_params_receiver)?;

            UserStreamInfo::pack(user_stream_info_updated, &mut user_stream_agreements_account.data.borrow_mut())?;
            UserStreamInfo::pack(receiver_stream_info_updated, &mut receiver_stream_agreements_account.data.borrow_mut())?;

            Ok(())
        }
        ///Function to stop a stream
        pub fn process_stop_stream(
            program_id: &Pubkey,
            accounts: &[AccountInfo],
        ) -> ProgramResult {
            let account_info_iter = &mut accounts.iter();
            let stream_token_info = next_account_info(account_info_iter)?;
            let authority_info = next_account_info(account_info_iter)?;
            let user_transfer_authority_info = next_account_info(account_info_iter)?;
            let user_stream_token_account = next_account_info(account_info_iter)?;
            let user_stream_agreements_account = next_account_info(account_info_iter)?;
            let receiver_stream_token_account = next_account_info(account_info_iter)?;
            let receiver_stream_agreements_account = next_account_info(account_info_iter)?;
            let token_program_info = next_account_info(account_info_iter)?;
    
            let stream_token_data = StreamVersion::unpack(&stream_token_info.data.borrow())?;
    
            // Self::check_accounts(
            //     stream_token_data.as_ref(),
            //     program_id,
            //     stream_token_info,
            //     authority_info,
            //     token_info,
            //     stream_token_mint_info,
            //     token_program_info,
            //     Some(source_a_info),
            //     None,
            // )?;
    
            let stream_token = Self::unpack_tokenccount(user_stream_token_account, stream_token_data.token_program_id())?;

            let stream_token_amount = stream_token.amount;

            let threshold_amount = 0u64;
            if stream_token_amount < threshold_amount {
                return Err(StreamTokenError::InsufficientFunds.into());
            }
            if stream_token_amount == 0 {
                return Err(StreamTokenError::ZeroTradingTokens.into());
            }

            let now = Clock::get()?.unix_timestamp as u64;
            let mut user_stream_info = UserStreamInfo::unpack(&user_stream_agreements_account.data.borrow())?;
            let mut receiver_stream_info = UserStreamInfo::unpack(&receiver_stream_agreements_account.data.borrow())?;

            if !user_stream_info.is_initialized {
                user_stream_info = UserStreamInfo::new(*stream_token_info.key)
            }
            let agreementInfo = BilateralStreamAgreement {
                flow_rate: 0u64,
                sender: *user_stream_token_account.key,
                receiver: *receiver_stream_token_account.key,
            };

            let mut add_stream_params_user = RemoveBilateralStreamParams{
                user_stream_info: user_stream_info,
                sender: *user_stream_token_account.key,
                receiver: *receiver_stream_token_account.key,
                is_user_sender: true,
                now:now,
            };

            let mut add_stream_params_receiver = RemoveBilateralStreamParams{
                user_stream_info: receiver_stream_info,
                sender: *user_stream_token_account.key,
                receiver: *receiver_stream_token_account.key,
                is_user_sender: false,
                now:now,
            };

            let user_stream_info_updated = agreementInfo.remove_stream(add_stream_params_user)?;
            let receiver_stream_info_updated = agreementInfo.remove_stream(add_stream_params_receiver)?;

            UserStreamInfo::pack(user_stream_info_updated, &mut user_stream_agreements_account.data.borrow_mut())?;
            UserStreamInfo::pack(receiver_stream_info_updated, &mut receiver_stream_agreements_account.data.borrow_mut())?;

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
                flow_rate,
            }) => {
                msg!("Instruction: StartStream");
                Self::process_start_stream(
                    program_id,
                    flow_rate,
                    accounts,
                )
            }
            SwapInstruction::StopStream(StopStream {
            }) => {
                msg!("Instruction: StartStream");
                Self::process_stop_stream(
                    program_id,
                    accounts,
                )
            }
           
        }
    }
}

impl PrintProgramError for StreamTokenError {
    fn print<E>(&self)
    where
        E: 'static + std::error::Error + DecodeError<E> + PrintProgramError + FromPrimitive,
    {
        match self {
            StreamTokenError::AlreadyInUse => msg!("Error: Swap account already in use"),
            StreamTokenError::InvalidProgramAddress => {
                msg!("Error: Invalid program address generated from nonce and key")
            }
            StreamTokenError::InvalidOwner => {
                msg!("Error: The input account owner is not the program address")
            }
            StreamTokenError::InvalidOutputOwner => {
                msg!("Error: Output pool account owner cannot be the program address")
            }
            StreamTokenError::ExpectedMint => msg!("Error: Deserialized account is not an SPL Token mint"),
            StreamTokenError::ExpectedAccount => {
                msg!("Error: Deserialized account is not an SPL Token account")
            }
            StreamTokenError::EmptySupply => msg!("Error: Input token account empty"),
            StreamTokenError::InvalidSupply => msg!("Error: Pool token mint has a non-zero supply"),
            StreamTokenError::RepeatedMint => msg!("Error: Swap input token accounts have the same mint"),
            StreamTokenError::InvalidDelegate => msg!("Error: Token account has a delegate"),
            StreamTokenError::InvalidInput => msg!("Error: InvalidInput"),
            StreamTokenError::IncorrectSwapAccount => {
                msg!("Error: Address of the provided swap token account is incorrect")
            }
            StreamTokenError::IncorrectPoolMint => {
                msg!("Error: Address of the provided pool token mint is incorrect")
            }
            StreamTokenError::InvalidOutput => msg!("Error: InvalidOutput"),
            StreamTokenError::CalculationFailure => msg!("Error: CalculationFailure"),
            StreamTokenError::InvalidInstruction => msg!("Error: InvalidInstruction"),
            StreamTokenError::ExceededSlippage => {
                msg!("Error: Swap instruction exceeds desired slippage limit")
            }
            StreamTokenError::InvalidCloseAuthority => msg!("Error: Token account has a close authority"),
            StreamTokenError::InvalidFreezeAuthority => {
                msg!("Error: Pool token mint has a freeze authority")
            }
            StreamTokenError::IncorrectFeeAccount => msg!("Error: Pool fee token account incorrect"),
            StreamTokenError::ZeroTradingTokens => {
                msg!("Error: Given pool token amount results in zero trading tokens")
            }
            StreamTokenError::FeeCalculationFailure => msg!(
                "Error: The fee calculation failed due to overflow, underflow, or unexpected 0"
            ),
            StreamTokenError::ConversionFailure => msg!("Error: Conversion to or from u64 failed."),
            StreamTokenError::InvalidFee => {
                msg!("Error: The provided fee does not match the program owner's constraints")
            }
            StreamTokenError::IncorrectTokenProgramId => {
                msg!("Error: The provided token program does not match the token program expected by the swap")
            }
            StreamTokenError::UnsupportedCurveType => {
                msg!("Error: The provided curve type is not supported by the program owner")
            }
            StreamTokenError::InvalidCurve => {
                msg!("Error: The provided curve parameters are invalid")
            }
            StreamTokenError::InsufficientFunds => {
                msg!("Error: The balance of input tokens is not enough")
            }
            StreamTokenError::UnsupportedCurveOperation => {
                msg!("Error: The operation cannot be performed on the given curve")
            }
        }
    }
}

fn to_u128(val: u64) -> Result<u128, StreamTokenError> {
    val.try_into().map_err(|_| StreamTokenError::ConversionFailure)
}

fn to_u64(val: u128) -> Result<u64, StreamTokenError> {
    val.try_into().map_err(|_| StreamTokenError::ConversionFailure)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instruction::{
            deposit_token, initialize,
            withdraw_token, start_stream
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

        // #[allow(clippy::too_many_arguments)]
        // pub fn start_stream(
        //     &mut self,
        //     user_key: &Pubkey,
        //     pool_key: &Pubkey,
        //     mut pool_account: &mut Account,
        //     token_key: &Pubkey,
        //     mut token_account: &mut Account,
        //     flow_rate: u64,
        // ) -> ProgramResult {
        //     let user_transfer_authority_key = Pubkey::new_unique();
        //     // approve user transfer authority to take out pool tokens
        //     do_process_instruction(
        //         approve(
        //             &spl_token::id(),
        //             pool_key,
        //             &user_transfer_authority_key,
        //             user_key,
        //             &[],
        //             tokenamount,
        //         )
        //         .unwrap(),
        //         vec![
        //             &mut pool_account,
        //             &mut Account::default(),
        //             &mut Account::default(),
        //         ],
        //     )
        //     .unwrap();

        //     // withdraw token a and b correctly
        //     do_process_instruction(
        //         start_stream(
                    
        //             StartStream {
        //                 flow_rate,
        //             },
        //         )
        //         .unwrap(),
        //         vec![
        //             &mut self.swap_account,
        //             &mut Account::default(),
        //             &mut Account::default(),
        //             &mut self.stream_token_mint_account,
        //             &mut pool_account,
        //             &mut self.token_account,
        //             &mut token_account,
        //             &mut self.stream_fee_account,
        //             &mut Account::default(),
        //         ],
        //     )
        // }
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
                Err(StreamTokenError::InvalidProgramAddress.into()),
                accounts.initialize_swap()
            );
            accounts.nonce = old_nonce;
        }

        // uninitialized token a account
        {
            let old_account = accounts.token_account;
            accounts.token_account = Account::new(0, 0, &spl_token::id());
            assert_eq!(
                Err(StreamTokenError::ExpectedAccount.into()),
                accounts.initialize_swap()
            );
            accounts.token_account = old_account;
        }

        // uninitialized pool mint
        {
            let old_account = accounts.stream_token_mint_account;
            accounts.stream_token_mint_account = Account::new(0, 0, &spl_token::id());
            assert_eq!(
                Err(StreamTokenError::ExpectedMint.into()),
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
                Err(StreamTokenError::InvalidOwner.into()),
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
                Err(StreamTokenError::InvalidOutputOwner.into()),
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
                Err(StreamTokenError::InvalidOutputOwner.into()),
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
                Err(StreamTokenError::InvalidOwner.into()),
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
                Err(StreamTokenError::InvalidFreezeAuthority.into()),
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
                Err(StreamTokenError::IncorrectTokenProgramId.into()),
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
                Err(StreamTokenError::EmptySupply.into()),
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
                Err(StreamTokenError::InvalidSupply.into()),
                accounts.initialize_swap()
            );

            // pool tokens already in circulation
            accounts.pool_tokenccount = empty_pool_tokenccount;
            assert_eq!(
                Err(StreamTokenError::InvalidSupply.into()),
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
                Err(StreamTokenError::IncorrectPoolMint.into()),
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
                Err(StreamTokenError::InvalidDelegate.into()),
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
                Err(StreamTokenError::InvalidCloseAuthority.into()),
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
                Err(StreamTokenError::IncorrectTokenProgramId.into()),
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
                Err(StreamTokenError::AlreadyInUse.into()),
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

    // #[test]
    // fn test_start_stream() {
    //     let user_key = Pubkey::new_unique();

    //     let sender_key = Pubkey::new_unique();
    //     let receiver_key = Pubkey::new_unique();
    //     let lamports = 10000000000u64;
    //     let agreement_account_size = 1000;
    //     let sender_agreement_account_key = Pubkey::new_unique();
    //     let receiver_agreement_account_key = Pubkey::new_unique();

    //     let initial_a = 100;
    //     let initial_pool =  1000;
    //     let withdraw_amount = 50;




    //     let mut accounts =
    //         SwapAccountInfo::new(&user_key, initial_a);

    //     accounts.initialize_swap().unwrap();

    //     // correct withdrawal
    //     {
    //         let (
    //             sender_token_key,
    //             mut sender_token_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &sender_key,
    //             initial_a,
    //             initial_pool.try_into().unwrap(),
    //         );

    //         let (
    //             receiver_token_key,
    //             mut receiver_token_account,
    //             pool_key,
    //             mut pool_account,
    //         ) = accounts.setup_tokenccounts(
    //             &user_key,
    //             &receiver_key,
    //             initial_a,
    //             initial_pool.try_into().unwrap(),
    //         );

    //         accounts
    //             .withdraw_token(
    //                 &withdrawer_key,
    //                 &pool_key,
    //                 &mut pool_account,
    //                 &token_key,
    //                 &mut token_account,
    //                 withdraw_amount.try_into().unwrap(),
    //             )
    //             .unwrap();

    //         let token =
    //             spl_token::state::Account::unpack(&accounts.token_account.data).unwrap();

    //         let stream_token_mint =
    //             spl_token::state::Mint::unpack(&accounts.stream_token_mint_account.data).unwrap();

    //         assert_eq!(
    //             token.amount,
    //             withdraw_amount
    //         );

    //         let token = spl_token::state::Account::unpack(&token_account.data).unwrap();
    //         assert_eq!(
    //             token.amount,
    //             initial_a + withdraw_amount
    //         );

    //         let pool_account = spl_token::state::Account::unpack(&pool_account.data).unwrap();
    //         assert_eq!(
    //             pool_account.amount,
    //             initial_pool - withdraw_amount
    //         );
    //     }
    // }
}
