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
    borrow::{Borrow, BorrowMut}
};

use crate::{
    error::StreamError,
    state::{UserStreamInfo,UserStreamBalance}
}; 

/// StreamAgreement
pub trait StreamAgreement {
    /// Add a new stream
    fn add_stream(&self, add_stream_params:AddBilateralStreamParams) -> Result<UserStreamInfo,ProgramError>;
    /// Remove existing stream
    fn remove_stream(&self, remove_stream_params:RemoveBilateralStreamParams) -> Result<UserStreamInfo,ProgramError>;    
    
}

/// BilateralStreamAgreement.
#[repr(C)]
#[derive(Debug, Default, PartialEq)]
pub struct BilateralStreamAgreement {
    /// Flow rate for a specific agreement
    pub flow_rate: u64,

    /// Sender of the tokens
    pub sender: Pubkey,

    /// Receiver of the tokens
    pub receiver: Pubkey,
}

/// Initialize an obligation
pub struct AddBilateralStreamParams {
    /// Last update to collateral, liquidity, or their market values
    pub user_stream_info: UserStreamInfo,
    /// Lending market address
    pub sender: Pubkey,
    /// Owner authority which can borrow liquidity
    pub receiver: Pubkey,
    /// isUserSender 
    pub is_user_sender: bool,
    /// Deposited collateral for the obligation, unique by deposit reserve address
    pub flow_rate: u64,
    /// Current timestamp
    pub now:u64,
}

/// Initialize an obligation
pub struct RemoveBilateralStreamParams {
    /// Last update to collateral, liquidity, or their market values
    pub user_stream_info: UserStreamInfo,
    /// Lending market address
    pub sender: Pubkey,
    /// Owner authority which can borrow liquidity
    pub receiver: Pubkey,
    /// isUserSender 
    pub is_user_sender: bool,
    /// Current timestamp
    pub now:u64,
}

impl StreamAgreement for BilateralStreamAgreement {
    fn add_stream(&self, mut add_stream_params:AddBilateralStreamParams) -> Result<UserStreamInfo,ProgramError> {
        let receiver = add_stream_params.receiver.borrow();
        let sender = add_stream_params.sender.borrow();

        let mut old_user_stream_info = add_stream_params.user_stream_info.borrow_mut();
        let mut old_stream_balance = old_user_stream_info.stream_balance.borrow_mut();
        let mut agreements:&mut Vec<BilateralStreamAgreement> = old_user_stream_info.agreements.borrow_mut();

        let mut new_deposit:i64 = 0i64;
        let mut new_owed_deposit:i64 = 0i64;
        let time_elapsed:u64 = add_stream_params.now-old_stream_balance.timestamp;

        let mut dynamic_balance:i64= 0i64 ;
        let new_flow_rate ;

        for agreement in agreements.iter() {
            if sender.eq(&agreement.sender) || receiver.eq(&agreement.receiver){
                return Err(StreamError::StreamAlreadyActive.into());
            }
        };

        new_deposit = old_stream_balance.deposit.
        checked_add(old_stream_balance.flow_rate.
            checked_mul(time_elapsed as i64).
            ok_or(StreamError::MathOverflowError)?
        ).ok_or(StreamError::MathOverflowError)?;


        if add_stream_params.is_user_sender{
            new_flow_rate = old_stream_balance.flow_rate.
            checked_sub(add_stream_params.flow_rate as i64).
            ok_or(StreamError::MathOverflowError)?;
        } else {
            new_flow_rate = old_stream_balance.flow_rate.
            checked_add(add_stream_params.flow_rate as i64).
            ok_or(StreamError::MathOverflowError)?;
        }
        let mut new_agreements = vec![BilateralStreamAgreement{
            flow_rate:add_stream_params.flow_rate,
            sender:*sender,
            receiver:*receiver,
        }];

        new_agreements.append(agreements);


        let new_user_stream_info = UserStreamInfo{
            is_initialized:true,
            stream_balance:UserStreamBalance{
                timestamp:add_stream_params.now,
                flow_rate:new_flow_rate,
                deposit:new_deposit,
                owed_deposit:new_owed_deposit,
            },
            agreements:new_agreements,
            stream_token_info_account:old_user_stream_info.stream_token_info_account,
        };

        return Ok(new_user_stream_info);
    }

    fn remove_stream(&self, mut remove_stream_params:RemoveBilateralStreamParams) -> Result<UserStreamInfo,ProgramError> {
        let receiver = remove_stream_params.receiver.borrow();
        let sender = remove_stream_params.sender.borrow();

        let mut old_user_stream_info = remove_stream_params.user_stream_info.borrow_mut();
        let mut old_stream_balance = old_user_stream_info.stream_balance.borrow_mut();
        let mut agreements:&mut Vec<BilateralStreamAgreement> = old_user_stream_info.agreements.borrow_mut();

        let mut new_deposit:i64 = 0i64;
        let mut new_owed_deposit:i64 = 0i64;
        let time_elapsed:u64 = remove_stream_params.now-old_stream_balance.timestamp;

        let mut dynamic_balance:i64= 0i64 ;
        let new_flow_rate ;
        let mut flow_rate_to_remove=0u64;
        let mut index:usize=0;

        let mut new_agreements = vec![];

        new_agreements.append(agreements);
        
        for agreement in agreements.iter() {
            if sender.eq(&agreement.sender) || receiver.eq(&agreement.receiver){
                new_agreements.remove(index);
                flow_rate_to_remove = agreement.flow_rate;
                break;
            }
            index=index+1;
        };

        new_deposit = old_stream_balance.deposit.
        checked_add(old_stream_balance.flow_rate.
            checked_mul(time_elapsed as i64).
            ok_or(StreamError::MathOverflowError)?
        ).ok_or(StreamError::MathOverflowError)?;


        if remove_stream_params.is_user_sender{
            new_flow_rate = old_stream_balance.flow_rate.
            checked_add(flow_rate_to_remove as i64).
            ok_or(StreamError::MathOverflowError)?;
        } else {
            new_flow_rate = old_stream_balance.flow_rate.
            checked_sub(flow_rate_to_remove as i64).
            ok_or(StreamError::MathOverflowError)?;
        }




        let new_user_stream_info = UserStreamInfo{
            is_initialized:true,
            stream_balance:UserStreamBalance{
                timestamp:remove_stream_params.now,
                flow_rate:new_flow_rate,
                deposit:new_deposit,
                owed_deposit:new_owed_deposit,
            },
            agreements:new_agreements,
            stream_token_info_account:old_user_stream_info.stream_token_info_account,
        };

        return Ok(new_user_stream_info);    } 

}

