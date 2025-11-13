use crate::abd::invariants::lin_queue::LinWriteToken;
use crate::abd::invariants::lin_queue::MaybeLinearized;
use crate::abd::proto::Timestamp;

use vstd::prelude::*;

verus! {

/// ABD read related errors
///
/// The only way an ABD read fails is when a quorum is known to be unatainable
/// This happens when a connection reset happens
/// In this case, the error is exposed to the client
pub enum ReadError<RL> {
    // The first read quorum failed
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        linearizer: Tracked<RL>
    },
    // The writeback phase of the read failed
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        linearizer: Tracked<RL>
    },
}

impl<RL> ReadError<RL> {
    pub open spec fn lin(self) -> Tracked<RL> {
        match self {
            ReadError::FailedFirstQuorum { linearizer, .. } => linearizer,
            ReadError::FailedSecondQuorum { linearizer, .. } => linearizer,
        }
    }
}


/// ABD write related errors
///
/// The only way an ABD write fails is when a quorum is known to be unatainable
/// This happens when a connection reset happens
/// In this case, the error is exposed to the client

pub enum WriteError<ML, MC, Op> {
    // The first phase of the write failed
    // In this case the write never physicially started, so we can get the MaybeLinearized
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeLinearized<ML, MC, Op>>,
    },

    // The second phase of the write failed
    // In this case the write is physically ongoing, so we can only return a token into the queue
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        timestamp: Timestamp,
        token: Tracked<LinWriteToken<ML>>,
    },
}

impl<RL> std::error::Error for ReadError<RL> {}
impl<ML, MC, Op> std::error::Error for WriteError<ML, MC, Op> {}
}

impl<RL> std::fmt::Debug for ReadError<RL> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::FailedFirstQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedFirstQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
            ReadError::FailedSecondQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedSecondQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
        }
    }
}

impl<RL> std::fmt::Display for ReadError<RL> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::FailedFirstQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the read; got {obtained} of {required} required responses"))
            },
            ReadError::FailedSecondQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the writeback phase of the read; got {obtained} of {required} required responses"))
            },
        }
    }
}

impl<ML, MC, Op> std::fmt::Debug for WriteError<ML, MC, Op> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WriteError::FailedFirstQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedFirstQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
            WriteError::FailedSecondQuorum {
                obtained, required, ..
            } => f
                .debug_struct("FailedSecondQuorum")
                .field("obtained", &obtained)
                .field("required", &required)
                .finish(),
        }
    }
}

impl<ML, MC, Op> std::fmt::Display for WriteError<ML, MC, Op> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WriteError::FailedFirstQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the first phase of the write; got {obtained} of {required} required responses"))
            },
            WriteError::FailedSecondQuorum { obtained, required, .. } => {
                f.write_fmt(format_args!("failed to obtain a quorum for the second phase of the write; got {obtained} of {required} required responses"))
            },
        }
    }
}
