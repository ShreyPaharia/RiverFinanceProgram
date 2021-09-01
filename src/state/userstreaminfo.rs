//! State(Agreement) transition types

use arrayref::{array_mut_ref, array_ref, array_refs, mut_array_refs};
use enum_dispatch::enum_dispatch;
use solana_program::{
    program_error::ProgramError,
    program_pack::{IsInitialized, Pack, Sealed},
    pubkey::Pubkey,
};
use std::{
    cmp::Ordering,
    convert::{TryFrom, TryInto},
};

use crate::{
    math::Rate,
    state::BilateralStreamAgreement,
};

// pub type UnixTimestamp = i64;


/// Program states.
#[repr(C)]
#[derive(Debug, Default, PartialEq)]
pub struct UserStreamBalance {
    /// Last update timestamp
    pub timestamp: u64,

    /// Net flow rate for a token
    pub flow_rate: i64,

    /// Accrued deposit from active agreements
    pub deposit: i64,

    /// Owed deposit from active agreements
    pub owed_deposit: i64,

}

/// User Stream Info.
#[repr(C)]
#[derive(Debug, Default, PartialEq)]
pub struct UserStreamInfo {
    /// Initialized state.
    pub is_initialized: bool,

    /// Flow rate for a specific agreement
    pub stream_balance: UserStreamBalance,

    /// Sender of the tokens
    pub agreements: Vec<BilateralStreamAgreement>,

    /// Stream token info
    pub stream_token_info_account: Pubkey,
}

const USER_STREAM_INFO_LEN: usize = 786; // 1+8+8+8+8+32+1+72*10
const AGREEMENT_LEN: usize =72; //8+32+32
const MAX_AGREEMENTS: usize = 10;

impl UserStreamInfo {
    /// Create a new obligation
    pub fn new(stream_token_info_key:Pubkey) -> Self {
        return UserStreamInfo {
            is_initialized: true,
            stream_balance: UserStreamBalance{
                timestamp: 0u64,
                flow_rate: 0i64,
                deposit: 0i64,
                owed_deposit: 0i64,
            },
            agreements: vec![],
            stream_token_info_account:stream_token_info_key,
        };
    }
}


impl Sealed for UserStreamInfo {}
impl IsInitialized for UserStreamInfo {
    fn is_initialized(&self) -> bool {
        self.is_initialized
    }
}
impl Pack for UserStreamInfo {
    const LEN: usize = USER_STREAM_INFO_LEN;
    
    fn pack_into_slice(&self, output: &mut [u8]) {
        let output = array_mut_ref![output, 0, USER_STREAM_INFO_LEN];
        let (
            is_initialized,
            timestamp,
            flow_rate,
            deposit,
            owed_deposit,
            stream_token_info_account,
            agreements_len,
            agreements_flat,
        ) = mut_array_refs![output, 1, 8, 8, 8, 8, 32, 1,AGREEMENT_LEN * MAX_AGREEMENTS];
        is_initialized[0] = self.is_initialized as u8;
        *timestamp = self.stream_balance.timestamp.to_le_bytes();
        *flow_rate = self.stream_balance.flow_rate.to_le_bytes();
        *deposit = self.stream_balance.deposit.to_le_bytes();
        stream_token_info_account.copy_from_slice(self.stream_token_info_account.as_ref());
        *owed_deposit = self.stream_balance.owed_deposit.to_le_bytes();
        *agreements_len = u8::try_from(self.agreements.len()).unwrap().to_le_bytes();

        let mut offset = 0;

        // agreements
        for agreement in &self.agreements {
            let agreement_flat = array_mut_ref![agreements_flat, offset, AGREEMENT_LEN];
            #[allow(clippy::ptr_offset_with_cast)]
            let (agreement_flow_rate, sender, receiver) =
                mut_array_refs![agreement_flat, 8, 32, 32];

            sender.copy_from_slice(agreement.sender.as_ref());
            receiver.copy_from_slice(agreement.receiver.as_ref());
            *agreement_flow_rate = agreement.flow_rate.to_le_bytes();

            offset += AGREEMENT_LEN;
        }
    }

    /// Unpacks a byte buffer into an [ObligationInfo](struct.ObligationInfo.html).
    fn unpack_from_slice(src: &[u8]) -> Result<Self, ProgramError> {
        let input = array_ref![src, 0, USER_STREAM_INFO_LEN];
        #[allow(clippy::ptr_offset_with_cast)]
        let (
            is_initialized,
            timestamp,
            flow_rate,
            deposit,
            owed_deposit,
            stream_token_info_account,
            agreements_len,
            agreements_flat,
        ) = array_refs![
            input,
            1,
            8,
            8,
            8,
            8,
            32,
            1,
            AGREEMENT_LEN * MAX_AGREEMENTS
        ];

        let agreements_len = u8::from_le_bytes(*agreements_len);
        let mut agreements = Vec::with_capacity(agreements_len as usize + 1);

        let mut offset = 0;
        for _ in 0..agreements_len {
            let agreement_flat = array_ref![agreements_flat, offset, AGREEMENT_LEN];
            #[allow(clippy::ptr_offset_with_cast)]
            let (agreement_flow_rate, sender, receiver) =
                    array_refs![agreement_flat, 8, 32, 32];
            agreements.push(BilateralStreamAgreement {
                flow_rate: u64::from_le_bytes(*agreement_flow_rate),
                sender: Pubkey::new(sender),
                receiver: Pubkey::new(receiver),
            });
            offset += AGREEMENT_LEN;
        }

        Ok(Self {
            is_initialized: match is_initialized {
                [0] => false,
                [1] => true,
                _ => return Err(ProgramError::InvalidAccountData),
            },
            stream_balance: UserStreamBalance{
                timestamp: u64::from_le_bytes(*timestamp),
                flow_rate: i64::from_le_bytes(*flow_rate),
                deposit: i64::from_le_bytes(*deposit),
                owed_deposit: i64::from_le_bytes(*owed_deposit),
            },
            agreements,
            stream_token_info_account:Pubkey::new_from_array(*stream_token_info_account),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::TryInto;

    const TEST_is_initialized:bool = true;
    const TEST_timestamp:u64 = 1u64;
    const TEST_flow_rate:i64 = 1i64;
    const TEST_deposit:i64 = 1i64;
    const TEST_owed_deposit:i64 = 1i64;

    const TEST_agreements_len:u8 = 2u8;

    const TEST_agreement_flow_rate1:u64 = 10u64;
    const TEST_agreement_flow_rate2:u64 = 5u64;

    const TEST_agreement_user: Pubkey = Pubkey::new_from_array([1u8; 32]);
    const TEST_agreement_sender1: Pubkey = Pubkey::new_from_array([2u8; 32]);
    const TEST_agreement_receiver2: Pubkey = Pubkey::new_from_array([3u8; 32]);
    const TEST_stream_token_info_account: Pubkey = Pubkey::new_from_array([4u8; 32]);



    #[test]
    fn user_stream_info_pack() {
        let TEST_agreements:Vec<BilateralStreamAgreement> = vec![
            BilateralStreamAgreement {
                flow_rate: TEST_agreement_flow_rate1,
                sender: TEST_agreement_sender1,
                receiver: TEST_agreement_user,
            },
            BilateralStreamAgreement {
                flow_rate: TEST_agreement_flow_rate2,
                sender: TEST_agreement_user,
                receiver: TEST_agreement_receiver2,
            }
        ];
        
        let user_stream_info = UserStreamInfo {
            is_initialized: TEST_is_initialized,
            stream_balance: UserStreamBalance{
                timestamp: TEST_timestamp,
                flow_rate: TEST_flow_rate,
                deposit: TEST_deposit,
                owed_deposit: TEST_owed_deposit,
            },
            agreements: TEST_agreements,
            stream_token_info_account:TEST_stream_token_info_account,
        };

        let mut packed = [0u8; UserStreamInfo::LEN];
        UserStreamInfo::pack(user_stream_info, &mut packed).unwrap();
        let unpacked = UserStreamInfo::unpack(&packed).unwrap();

        assert!(unpacked.is_initialized());
        assert_eq!(unpacked.stream_balance.timestamp, TEST_timestamp);
        assert_eq!(unpacked.stream_balance.flow_rate, TEST_flow_rate);
        assert_eq!(unpacked.stream_balance.deposit, TEST_deposit);
        assert_eq!(unpacked.stream_balance.owed_deposit, TEST_owed_deposit);
        assert_eq!(unpacked.agreements[0].flow_rate, TEST_agreement_flow_rate1);
        assert_eq!(unpacked.agreements[0].sender, TEST_agreement_sender1);
        assert_eq!(unpacked.agreements[0].receiver, TEST_agreement_user);
        assert_eq!(unpacked.agreements[1].flow_rate, TEST_agreement_flow_rate2);
        assert_eq!(unpacked.agreements[1].sender, TEST_agreement_user);
        assert_eq!(unpacked.agreements[1].receiver, TEST_agreement_receiver2);

        assert_eq!(unpacked.stream_token_info_account, TEST_stream_token_info_account);


        
    }

}
