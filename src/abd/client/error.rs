use crate::abd::invariants::lin_queue::MaybeLinearized;
use crate::abd::invariants::logatom::RegisterWrite;

use vstd::logatom::MutLinearizer;
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
// TODO(failed-write): handling a provably failed write (multiple channels were closed at
// send time) is hard.
//
// A write that fails on the first round can safely recover either the linearizer or the completion
// A write that fails on the second round is more complicated:
//  - on the one hand it has not returned
//  - however, it must remain in the queue
pub enum WriteError<ML: MutLinearizer<RegisterWrite>> {
    // The first phase of the write failed
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeLinearized<ML>>,
    },

    // The second phase of the write failed
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        /* token: Tracked<LinToken> */
    },
}

impl<RL> std::error::Error for ReadError<RL> {}
impl<ML: MutLinearizer<RegisterWrite>> std::error::Error for WriteError<ML> {}
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

impl<ML: MutLinearizer<RegisterWrite>> std::fmt::Debug for WriteError<ML> {
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

impl<ML: MutLinearizer<RegisterWrite>> std::fmt::Display for WriteError<ML> {
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
