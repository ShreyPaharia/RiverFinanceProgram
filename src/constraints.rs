//! Various constraints as required for production environments

use crate::{
    error::StreamError,
};

use solana_program::program_error::ProgramError;

#[cfg(feature = "production")]
use std::env;

/// Encodes fee constraints, used in multihost environments where the program
/// may be used by multiple frontends, to ensure that proper fees are being
/// assessed.
/// Since this struct needs to be created at compile-time, we only have access
/// to const functions and constructors. Since SwapCurve contains a Box, it
/// cannot be used, so we have to split the curves based on their types.
pub struct Constraints<'a> {
    /// Owner of the program
    pub owner_key: &'a str,
}

impl<'a> Constraints<'a> {

}

#[cfg(feature = "production")]
const OWNER_KEY: &str = env!("SWAP_PROGRAM_OWNER_FEE_ADDRESS");


/// Fee structure defined by program creator in order to enforce certain
/// fees when others use the program.  Adds checks on pool creation and
/// swapping to ensure the correct fees and account owners are passed.
/// Fees provided during production build currently are considered min
/// fees that creator of the pool can specify. Host fee is a fixed
/// percentage that host receives as a portion of owner fees
pub const SWAP_CONSTRAINTS: Option<Constraints> = {
    #[cfg(feature = "production")]
    {
        Some(Constraints {
            owner_key: OWNER_KEY,
        })
    }
    #[cfg(not(feature = "production"))]
    {
        None
    }
};
