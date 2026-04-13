use std::error::Error;
use std::fmt::Debug;
use std::fmt::Display;

use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::std_specs::convert::FromSpecImpl;

verus! {

#[derive(Debug)]
pub enum TryListenError {
    Empty,
    Disconnected,
}

#[derive(Debug)]
pub enum TryRecvError {
    Empty,
    Disconnected,
}

#[derive(Debug)]
pub struct SendError<S>(pub S);

#[derive(Debug)]
pub enum InvokeError<S> {
    SendError(S),
    Disconnected,
    Empty,
}

#[derive(Debug)]
pub struct ConnectError;

impl Error for TryListenError {

}

impl Error for TryRecvError {

}

impl<S: Display + Debug> Error for SendError<S> {

}

impl Error for ConnectError {

}

impl<S: Display + Debug> Error for InvokeError<S> {

}

impl<S> From<SendError<S>> for InvokeError<S> {
    fn from(value: SendError<S>) -> InvokeError<S> {
        InvokeError::SendError(value.0)
    }
}

#[cfg(verus_only)]
impl<S> FromSpecImpl<SendError<S>> for InvokeError<S> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: SendError<S>) -> InvokeError<S> {
        InvokeError::SendError(value.0)
    }
}

impl<S> From<TryRecvError> for InvokeError<S> {
    fn from(value: TryRecvError) -> InvokeError<S> {
        match value {
            TryRecvError::Empty => InvokeError::Empty,
            TryRecvError::Disconnected => InvokeError::Disconnected,
        }
    }
}

#[cfg(verus_only)]
impl<S> FromSpecImpl<TryRecvError> for InvokeError<S> {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(value: TryRecvError) -> InvokeError<S> {
        match value {
            TryRecvError::Empty => InvokeError::Empty,
            TryRecvError::Disconnected => InvokeError::Disconnected,
        }
    }
}

} // verus!
impl Display for TryListenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TryListenError::Empty => f.write_str("TryListenError: no message came"),
            TryListenError::Disconnected => f.write_str("TryListenError: listenning channel broke"),
        }
    }
}

impl Display for TryRecvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TryRecvError::Empty => f.write_str("TryRecvError: no message came"),
            TryRecvError::Disconnected => f.write_str("TryRecvError: channel broke"),
        }
    }
}

impl<S: Display> Display for SendError<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SendError: ")?;
        self.0.fmt(f)
    }
}

impl Display for ConnectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Error connecting")
    }
}

impl<S: Display> Display for InvokeError<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvokeError::SendError(s) => {
                f.write_str("InvokeError: failed to send; ")?;
                s.fmt(f)
            }
            InvokeError::Empty => f.write_str("InvokeError: no reply came"),
            InvokeError::Disconnected => f.write_str("InvokeError: channel broke"),
        }
    }
}
