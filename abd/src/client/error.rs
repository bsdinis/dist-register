use crate::invariants::committed_to::WriteCommitment;
use crate::invariants::lin_queue::LinWriteToken;
use crate::invariants::lin_queue::MaybeReadLinearized;
use crate::invariants::lin_queue::MaybeWriteLinearized;
use crate::timestamp::Timestamp;

use specs::abd::AbdError;
use specs::abd::RegisterRead;
use specs::abd::RegisterWrite;

use vstd::logatom::MutLinearizer;
use vstd::logatom::ReadLinearizer;
use vstd::prelude::*;

verus! {

/// ABD read related errors
///
/// The only way an ABD read fails is when a quorum is known to be unatainable
/// This happens when a connection reset happens
/// In this case, the error is exposed to the client
pub enum ReadError<RL, RC> {
    // The first read quorum failed
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeReadLinearized<RL, RC>>,
    },
    // The writeback phase of the read failed
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeReadLinearized<RL, RC>>,
    },
}

/// ABD write related errors
///
/// The only way an ABD write fails is when a quorum is known to be unatainable
/// This happens when a connection reset happens
/// In this case, the error is exposed to the client
pub enum WriteError<ML, MC> {
    // The first phase of the write failed
    // In this case the write never physicially started, so we can get the MaybeLinearized
    FailedFirstQuorum {
        obtained: usize,
        required: usize,
        lincomp: Tracked<MaybeWriteLinearized<ML, MC>>,
    },
    // The second phase of the write failed
    // In this case the write is physically ongoing, so we can only return a token into the queue
    FailedSecondQuorum {
        obtained: usize,
        required: usize,
        timestamp: Timestamp,
        token: Tracked<LinWriteToken<ML>>,
        commitment: Tracked<WriteCommitment>,
    },
}

impl<ML> WriteError<ML, ML::Completion> where ML: MutLinearizer<RegisterWrite> {
    pub open spec fn inv(self) -> bool {
        match self {
            WriteError::FailedFirstQuorum { lincomp, .. } => { lincomp@.inv() },
            WriteError::FailedSecondQuorum { token, commitment, timestamp, .. } => {
                &&& token@.key() == timestamp
                &&& commitment@.key() == timestamp
                &&& commitment@.value() == token@.value().op.new_value
            },
        }
    }
}

impl<RL, RC> std::error::Error for ReadError<RL, RC> {

}

impl<ML, MC> std::error::Error for WriteError<ML, MC> {

}

impl<RL> AbdError<RL, RegisterRead> for ReadError<RL, RL::Completion> where
    RL: ReadLinearizer<RegisterRead>,
 {
    open spec fn err_ensures(self, op: RegisterRead, lin: RL) -> bool {
        &&& self is FailedFirstQuorum ==> ({
            &&& self->FailedFirstQuorum_lincomp@.lin() == lin
            &&& self->FailedFirstQuorum_lincomp@.op() == op
        })
        &&& self is FailedSecondQuorum ==> ({
            &&& self->FailedSecondQuorum_lincomp@.lin() == lin
            &&& self->FailedSecondQuorum_lincomp@.op() == op
        })
    }
}

impl<ML> AbdError<ML, RegisterWrite> for WriteError<ML, ML::Completion> where
    ML: MutLinearizer<RegisterWrite>,
 {
    open spec fn err_ensures(self, op: RegisterWrite, lin: ML) -> bool {
        &&& self.inv()
        &&& self is FailedFirstQuorum ==> ({
            &&& self->lincomp@.lin() == lin
            &&& self->lincomp@.op() == op
        })
        &&& self is FailedSecondQuorum ==> ({
            &&& self->token@.value().lin == lin
            &&& self->token@.value().op == op
        })
    }
}

} // verus!
impl<RL, RC> std::fmt::Debug for ReadError<RL, RC> {
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

impl<RL, RC> std::fmt::Display for ReadError<RL, RC> {
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

impl<ML, MC> std::fmt::Debug for WriteError<ML, MC> {
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

impl<ML, MC> std::fmt::Display for WriteError<ML, MC> {
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
