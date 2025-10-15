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
// The crux is that the linearizer may be applied by either a subsequent write or read (in both cases).
// If the second round failed, we can return the token for the linearizer:
// - Offer a call to wait on the linearization token (from the timestamp)
// - Extract the completion
//
// For the first round, it's harder, because the timestamp at this point is prophecized, with no
// good way to be resolved.
//
// - nits:
//      - the token has no way to relate to the watermark
//      - in the case of a failed first quorum we never actually resolve the timestamp of the call
//      - maybe the prophecy timestamp needs to be returned too?
//      - sounds complicated and of dubious usefulness -- but this would be the place to put it
#[derive(Debug)]
pub enum WriteError {
    // The first phase of the write failed
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        /* linearizer: Tracked<ML> */
        /* completion: Tracked<ML::Completion> */
        /* token: Tracked<int> */
    },

    // The second phase of the write failed
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        /* linearizer: Tracked<ML> */
        /* completion: Tracked<ML::Completion> */
        /* token: Tracked<int> */
    },
}

impl<RL> std::error::Error for ReadError<RL> {}
impl std::error::Error for WriteError {}
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

impl std::fmt::Display for WriteError {
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
