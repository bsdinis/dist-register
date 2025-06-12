use vstd::prelude::*;

verus! {
#[derive(Debug)]
pub enum Error {
    FailedFirstQuorum { obtained: usize, required: usize },
    FailedSecondQuorum { obtained: usize, required: usize },
}

impl std::error::Error for Error {}
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::FailedFirstQuorum { obtained, required } =>
        f.write_fmt(format_args!("failed to obtain a quorum for the first round; got {obtained} of {required} required responses")),
            Error::FailedSecondQuorum { obtained, required } =>
        f.write_fmt(format_args!("failed to obtain a quorum for the second round; got {obtained} of {required} required responses"))
        }
    }
}
