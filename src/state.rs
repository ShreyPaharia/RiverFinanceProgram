//! State transition types

use arrayref::{array_mut_ref, array_ref, array_refs, mut_array_refs};
use enum_dispatch::enum_dispatch;
use solana_program::{
    program_error::ProgramError,
    program_pack::{IsInitialized, Pack, Sealed},
    pubkey::Pubkey,
};

/// Trait representing access to program state across all versions
#[enum_dispatch]
pub trait StreamState {
    /// Is the swap initialized, with data written to it
    fn is_initialized(&self) -> bool;
    /// Bump seed used to generate the program address / authority
    fn nonce(&self) -> u8;
    /// Token program ID associated with the swap
    fn token_program_id(&self) -> &Pubkey;
    /// Address of token A liquidity account
    fn token_account(&self) -> &Pubkey;

    /// Address of pool token mint
    fn stream_token_mint(&self) -> &Pubkey;

    /// Address of token A mint
    fn token_mint(&self) -> &Pubkey;

    /// Address of pool fee account
    fn stream_fee_account(&self) -> &Pubkey;

}

/// All versions of StreamState
#[enum_dispatch(StreamState)]
pub enum StreamVersion {
    /// Latest version, used for all new swaps
    StreamV1,
}

/// StreamVersion does not implement program_pack::Pack because there are size
/// checks on pack and unpack that would break backwards compatibility, so
/// special implementations are provided here
impl StreamVersion {
    /// Size of the latest version of the StreamState
    pub const LATEST_LEN: usize = 1 + StreamV1::LEN; // add one for the version enum

    /// Pack a swap into a byte array, based on its version
    pub fn pack(src: Self, dst: &mut [u8]) -> Result<(), ProgramError> {
        match src {
            Self::StreamV1(swap_info) => {
                dst[0] = 1;
                StreamV1::pack(swap_info, &mut dst[1..])
            }
        }
    }

    /// Unpack the swap account based on its version, returning the result as a
    /// StreamState trait object
    pub fn unpack(input: &[u8]) -> Result<Box<dyn StreamState>, ProgramError> {
        let (&version, rest) = input
            .split_first()
            .ok_or(ProgramError::InvalidAccountData)?;
        match version {
            1 => Ok(Box::new(StreamV1::unpack(rest)?)),
            _ => Err(ProgramError::UninitializedAccount),
        }
    }

    /// Special check to be done before any instruction processing, works for
    /// all versions
    pub fn is_initialized(input: &[u8]) -> bool {
        match Self::unpack(input) {
            Ok(swap) => swap.is_initialized(),
            Err(_) => false,
        }
    }
}

/// Program states.
#[repr(C)]
#[derive(Debug, Default, PartialEq)]
pub struct StreamV1 {
    /// Initialized state.
    pub is_initialized: bool,
    /// Nonce used in program address.
    /// The program address is created deterministically with the nonce,
    /// swap program id, and swap account pubkey.  This program address has
    /// authority over the swap's token A account, token B account, and pool
    /// token mint.
    pub nonce: u8,

    /// Program ID of the tokens being exchanged.
    pub token_program_id: Pubkey,

    /// Token A
    pub token: Pubkey,

    /// Pool tokens are issued when A or B tokens are deposited.
    /// Pool tokens can be withdrawn back to the original A or B token.
    pub stream_token_mint: Pubkey,

    /// Mint information for token A
    pub token_mint: Pubkey,

    /// Pool token account to receive trading and / or withdrawal fees
    pub stream_fee_account: Pubkey,

}

impl StreamState for StreamV1 {
    fn is_initialized(&self) -> bool {
        self.is_initialized
    }

    fn nonce(&self) -> u8 {
        self.nonce
    }

    fn token_program_id(&self) -> &Pubkey {
        &self.token_program_id
    }

    fn token_account(&self) -> &Pubkey {
        &self.token
    }

    fn stream_token_mint(&self) -> &Pubkey {
        &self.stream_token_mint
    }

    fn token_mint(&self) -> &Pubkey {
        &self.token_mint
    }

    fn stream_fee_account(&self) -> &Pubkey {
        &self.stream_fee_account
    }
}

impl Sealed for StreamV1 {}
impl IsInitialized for StreamV1 {
    fn is_initialized(&self) -> bool {
        self.is_initialized
    }
}

impl Pack for StreamV1 {
    const LEN: usize = 162;

    
    fn pack_into_slice(&self, output: &mut [u8]) {
        let output = array_mut_ref![output, 0, 162];
        let (
            is_initialized,
            nonce,
            token_program_id,
            token,
            stream_token_mint,
            token_mint,
            stream_fee_account,
        ) = mut_array_refs![output, 1, 1, 32, 32, 32, 32, 32];
        is_initialized[0] = self.is_initialized as u8;
        nonce[0] = self.nonce;
        token_program_id.copy_from_slice(self.token_program_id.as_ref());
        token.copy_from_slice(self.token.as_ref());
        stream_token_mint.copy_from_slice(self.stream_token_mint.as_ref());
        token_mint.copy_from_slice(self.token_mint.as_ref());
        stream_fee_account.copy_from_slice(self.stream_fee_account.as_ref());
    }

    /// Unpacks a byte buffer into a [StreamV1](struct.StreamV1.html).
    fn unpack_from_slice(input: &[u8]) -> Result<Self, ProgramError> {
        let input = array_ref![input, 0, 162];
        #[allow(clippy::ptr_offset_with_cast)]
        let (
            is_initialized,
            nonce,
            token_program_id,
            token,
            stream_token_mint,
            token_mint,
            stream_fee_account,
        ) = array_refs![input, 1, 1, 32, 32, 32, 32, 32];
        Ok(Self {
            is_initialized: match is_initialized {
                [0] => false,
                [1] => true,
                _ => return Err(ProgramError::InvalidAccountData),
            },
            nonce: nonce[0],
            token_program_id: Pubkey::new_from_array(*token_program_id),
            token: Pubkey::new_from_array(*token),
            stream_token_mint: Pubkey::new_from_array(*stream_token_mint),
            token_mint: Pubkey::new_from_array(*token_mint),
            stream_fee_account: Pubkey::new_from_array(*stream_fee_account),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryInto;

    const TEST_NONCE: u8 = 255;
    const TEST_TOKEN_PROGRAM_ID: Pubkey = Pubkey::new_from_array([1u8; 32]);
    const TEST_token: Pubkey = Pubkey::new_from_array([2u8; 32]);
    const TEST_stream_token_mint: Pubkey = Pubkey::new_from_array([3u8; 32]);
    const TEST_token_MINT: Pubkey = Pubkey::new_from_array([4u8; 32]);
    const TEST_stream_fee_account: Pubkey = Pubkey::new_from_array([5u8; 32]);

    #[test]
    fn stream_version_pack() {

        let swap_info = StreamVersion::StreamV1(StreamV1 {
            is_initialized: true,
            nonce: TEST_NONCE,
            token_program_id: TEST_TOKEN_PROGRAM_ID,
            token: TEST_token,
            stream_token_mint: TEST_stream_token_mint,
            token_mint: TEST_token_MINT,
            stream_fee_account: TEST_stream_fee_account,
        });

        let mut packed = [0u8; StreamVersion::LATEST_LEN];
        StreamVersion::pack(swap_info, &mut packed).unwrap();
        let unpacked = StreamVersion::unpack(&packed).unwrap();

        assert!(unpacked.is_initialized());
        assert_eq!(unpacked.nonce(), TEST_NONCE);
        assert_eq!(*unpacked.token_program_id(), TEST_TOKEN_PROGRAM_ID);
        assert_eq!(*unpacked.token_account(), TEST_token);
        assert_eq!(*unpacked.stream_token_mint(), TEST_stream_token_mint);
        assert_eq!(*unpacked.token_mint(), TEST_token_MINT);
        assert_eq!(*unpacked.stream_fee_account(), TEST_stream_fee_account);
    }

    #[test]
    fn stream_v1_pack() {
        let swap_info = StreamV1 {
            is_initialized: true,
            nonce: TEST_NONCE,
            token_program_id: TEST_TOKEN_PROGRAM_ID,
            token: TEST_token,
            stream_token_mint: TEST_stream_token_mint,
            token_mint: TEST_token_MINT,
            stream_fee_account: TEST_stream_fee_account,
        };

        let mut packed = [0u8; StreamV1::LEN];
        StreamV1::pack_into_slice(&swap_info, &mut packed);
        let unpacked = StreamV1::unpack(&packed).unwrap();
        assert_eq!(swap_info, unpacked);

        let mut packed = vec![1u8, TEST_NONCE];
        packed.extend_from_slice(&TEST_TOKEN_PROGRAM_ID.to_bytes());
        packed.extend_from_slice(&TEST_token.to_bytes());
        packed.extend_from_slice(&TEST_stream_token_mint.to_bytes());
        packed.extend_from_slice(&TEST_token_MINT.to_bytes());
        packed.extend_from_slice(&TEST_stream_fee_account.to_bytes());
        let unpacked = StreamV1::unpack(&packed).unwrap();
        assert_eq!(swap_info, unpacked);

        let packed = [0u8; StreamV1::LEN];
        let swap_info: StreamV1 = Default::default();
        let unpack_unchecked = StreamV1::unpack_unchecked(&packed).unwrap();
        assert_eq!(unpack_unchecked, swap_info);
        let err = StreamV1::unpack(&packed).unwrap_err();
        assert_eq!(err, ProgramError::UninitializedAccount);
    }
}
