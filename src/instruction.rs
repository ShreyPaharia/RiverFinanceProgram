//! Instruction types

#![allow(clippy::too_many_arguments)]

use crate::error::StreamError;
use solana_program::{
    instruction::{AccountMeta, Instruction},
    program_error::ProgramError,
    program_pack::Pack,
    pubkey::Pubkey,
};
use std::convert::TryInto;
use std::mem::size_of;

#[cfg(feature = "fuzz")]
use arbitrary::Arbitrary;

/// Initialize instruction data
#[repr(C)]
#[derive(Debug, PartialEq)]
pub struct Initialize {
    /// nonce used to create valid program address
    pub nonce: u8,
}

/// DepositToken instruction data
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
#[repr(C)]
#[derive(Clone, Debug, PartialEq)]
pub struct DepositToken {
    /// Pool token amount to transfer. token and token_b amount are set by
    /// the current exchange rate and size of the pool
    pub pool_tokenmount: u64,
}

/// WithdrawToken instruction data
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
#[repr(C)]
#[derive(Clone, Debug, PartialEq)]
pub struct WithdrawToken {
    /// Amount of pool tokens to burn. User receives an output of token a
    /// and b based on the percentage of the pool tokens that are returned.
    pub pool_tokenmount: u64,
}

/// Instructions supported by the token swap program.
#[repr(C)]
#[derive(Debug, PartialEq)]
pub enum SwapInstruction {
    ///   Initializes a new swap
    ///
    ///   0. `[writable, signer]` New Token-swap to create.
    ///   1. `[]` swap authority derived from `create_program_address(&[Token-swap account])`
    ///   2. `[]` token Account. Must be non zero, owned by swap authority.
    ///   3. `[]` token_b Account. Must be non zero, owned by swap authority.
    ///   4. `[writable]` Pool Token Mint. Must be empty, owned by swap authority.
    ///   5. `[]` Pool Token Account to deposit trading and withdraw fees.
    ///   Must be empty, not owned by swap authority
    ///   6. `[writable]` Pool Token Account to deposit the initial pool token
    ///   supply.  Must be empty, not owned by swap authority.
    ///   7. '[]` Token program id
    Initialize(Initialize),

    ///   Deposit both types of tokens into the pool.  The output is a "pool"
    ///   token representing ownership in the pool. Inputs are converted to
    ///   the current ratio.
    ///
    ///   0. `[]` Token-swap
    ///   1. `[]` swap authority
    ///   2. `[]` user transfer authority
    ///   3. `[writable]` token user transfer authority can transfer amount,
    ///   4. `[writable]` token_b user transfer authority can transfer amount,
    ///   5. `[writable]` token Base Account to deposit into.
    ///   6. `[writable]` token_b Base Account to deposit into.
    ///   7. `[writable]` Pool MINT account, swap authority is the owner.
    ///   8. `[writable]` Pool Account to deposit the generated tokens, user is the owner.
    ///   9. '[]` Token program id
    DepositToken(DepositToken),

    ///   Withdraw both types of tokens from the pool at the current ratio, given
    ///   pool tokens.  The pool tokens are burned in exchange for an equivalent
    ///   amount of token A and B.
    ///
    ///   0. `[]` Token-swap
    ///   1. `[]` swap authority
    ///   2. `[]` user transfer authority
    ///   3. `[writable]` Pool mint account, swap authority is the owner
    ///   4. `[writable]` SOURCE Pool account, amount is transferable by user transfer authority.
    ///   5. `[writable]` token Swap Account to withdraw FROM.
    ///   6. `[writable]` token_b Swap Account to withdraw FROM.
    ///   7. `[writable]` token user Account to credit.
    ///   8. `[writable]` token_b user Account to credit.
    ///   9. `[writable]` Fee account, to receive withdrawal fees
    ///   10 '[]` Token program id
    WithdrawToken(WithdrawToken),
}

impl SwapInstruction {
    /// Unpacks a byte buffer into a [SwapInstruction](enum.SwapInstruction.html).
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        let (&tag, rest) = input.split_first().ok_or(StreamError::InvalidInstruction)?;
        Ok(match tag {
            0 => {
                let (&nonce, rest) = rest.split_first().ok_or(StreamError::InvalidInstruction)?;
                Self::Initialize(Initialize {
                    nonce
                })
            }
            1 => {
                let (pool_tokenmount, rest) = Self::unpack_u64(rest)?;
                Self::DepositToken(DepositToken {
                    pool_tokenmount
                })
            }
            2 => {
                let (pool_tokenmount, rest) = Self::unpack_u64(rest)?;
                Self::WithdrawToken(WithdrawToken {
                    pool_tokenmount,
                })
            }
            _ => return Err(StreamError::InvalidInstruction.into()),
        })
    }

    fn unpack_u64(input: &[u8]) -> Result<(u64, &[u8]), ProgramError> {
        if input.len() >= 8 {
            let (amount, rest) = input.split_at(8);
            let amount = amount
                .get(..8)
                .and_then(|slice| slice.try_into().ok())
                .map(u64::from_le_bytes)
                .ok_or(StreamError::InvalidInstruction)?;
            Ok((amount, rest))
        } else {
            Err(StreamError::InvalidInstruction.into())
        }
    }

    /// Packs a [SwapInstruction](enum.SwapInstruction.html) into a byte buffer.
    pub fn pack(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(size_of::<Self>());
        match &*self {
            Self::Initialize(Initialize {
                nonce
            }) => {
                buf.push(0);
                buf.push(*nonce);
            }
            Self::DepositToken(DepositToken {
                pool_tokenmount,
            }) => {
                buf.push(1);
                buf.extend_from_slice(&pool_tokenmount.to_le_bytes());
            }
            Self::WithdrawToken(WithdrawToken {
                pool_tokenmount,
            }) => {
                buf.push(2);
                buf.extend_from_slice(&pool_tokenmount.to_le_bytes());
            }
        }
        buf
    }
}

/// Creates an 'initialize' instruction.
pub fn initialize(
    program_id: &Pubkey,
    token_program_id: &Pubkey,
    swap_pubkey: &Pubkey,
    authority_pubkey: &Pubkey,
    token_pubkey: &Pubkey,
    pool_pubkey: &Pubkey,
    fee_pubkey: &Pubkey,
    destination_pubkey: &Pubkey,
    nonce: u8,
) -> Result<Instruction, ProgramError> {
    let init_data = SwapInstruction::Initialize(Initialize {
        nonce,
    });
    let data = init_data.pack();

    let accounts = vec![
        AccountMeta::new(*swap_pubkey, true),
        AccountMeta::new_readonly(*authority_pubkey, false),
        AccountMeta::new_readonly(*token_pubkey, false),
        AccountMeta::new(*pool_pubkey, false),
        AccountMeta::new_readonly(*fee_pubkey, false),
        AccountMeta::new(*destination_pubkey, false),
        AccountMeta::new_readonly(*token_program_id, false),
    ];

    Ok(Instruction {
        program_id: *program_id,
        accounts,
        data,
    })
}

/// Creates a 'deposit_token' instruction.
pub fn deposit_token(
    program_id: &Pubkey,
    token_program_id: &Pubkey,
    swap_pubkey: &Pubkey,
    authority_pubkey: &Pubkey,
    user_transfer_authority_pubkey: &Pubkey,
    deposit_token_pubkey: &Pubkey,
    swap_token_pubkey: &Pubkey,
    stream_token_mint_pubkey: &Pubkey,
    destination_pubkey: &Pubkey,
    instruction: DepositToken,
) -> Result<Instruction, ProgramError> {
    let data = SwapInstruction::DepositToken(instruction).pack();

    let accounts = vec![
        AccountMeta::new_readonly(*swap_pubkey, false),
        AccountMeta::new_readonly(*authority_pubkey, false),
        AccountMeta::new_readonly(*user_transfer_authority_pubkey, true),
        AccountMeta::new(*deposit_token_pubkey, false),
        AccountMeta::new(*swap_token_pubkey, false),
        AccountMeta::new(*stream_token_mint_pubkey, false),
        AccountMeta::new(*destination_pubkey, false),
        AccountMeta::new_readonly(*token_program_id, false),
    ];

    Ok(Instruction {
        program_id: *program_id,
        accounts,
        data,
    })
}

/// Creates a 'withdraw_token' instruction.
pub fn withdraw_token(
    program_id: &Pubkey,
    token_program_id: &Pubkey,
    swap_pubkey: &Pubkey,
    authority_pubkey: &Pubkey,
    user_transfer_authority_pubkey: &Pubkey,
    stream_token_mint_pubkey: &Pubkey,
    fee_account_pubkey: &Pubkey,
    source_pubkey: &Pubkey,
    swap_token_pubkey: &Pubkey,
    destination_token_pubkey: &Pubkey,
    instruction: WithdrawToken,
) -> Result<Instruction, ProgramError> {
    let data = SwapInstruction::WithdrawToken(instruction).pack();

    let accounts = vec![
        AccountMeta::new_readonly(*swap_pubkey, false),
        AccountMeta::new_readonly(*authority_pubkey, false),
        AccountMeta::new_readonly(*user_transfer_authority_pubkey, true),
        AccountMeta::new(*stream_token_mint_pubkey, false),
        AccountMeta::new(*source_pubkey, false),
        AccountMeta::new(*swap_token_pubkey, false),
        AccountMeta::new(*destination_token_pubkey, false),
        AccountMeta::new(*fee_account_pubkey, false),
        AccountMeta::new_readonly(*token_program_id, false),
    ];

    Ok(Instruction {
        program_id: *program_id,
        accounts,
        data,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_intialize() {

        let nonce: u8 = 255;
        let amp: u64 = 1;
        let check = SwapInstruction::Initialize(Initialize {
            nonce
        });
        let packed = check.pack();
        let mut expect = vec![0u8, nonce];
        assert_eq!(packed, expect);
        let unpacked = SwapInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);
    }

    #[test]
    fn pack_deposit() {
        let pool_tokenmount: u64 = 5;
        let check = SwapInstruction::DepositToken(DepositToken {
            pool_tokenmount,
        });
        let packed = check.pack();
        let mut expect = vec![1];
        expect.extend_from_slice(&pool_tokenmount.to_le_bytes());
        assert_eq!(packed, expect);
        let unpacked = SwapInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);
    }

    #[test]
    fn pack_withdraw() {
        let pool_tokenmount: u64 = 1212438012089;
        let minimum_token_amount: u64 = 102198761982612;
        let check = SwapInstruction::WithdrawToken(WithdrawToken {
            pool_tokenmount,
        });
        let packed = check.pack();
        let mut expect = vec![2];
        expect.extend_from_slice(&pool_tokenmount.to_le_bytes());
        assert_eq!(packed, expect);
        let unpacked = SwapInstruction::unpack(&expect).unwrap();
        assert_eq!(unpacked, check);
    }
}