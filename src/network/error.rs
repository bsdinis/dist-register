use std::error::Error;
use std::fmt::Debug;
use std::fmt::Display;

use vstd::prelude::*;

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
pub struct ConnectError;

impl Error for TryListenError {}

impl Error for TryRecvError {}

impl<S: Display + Debug> Error for SendError<S> {}

impl Error for ConnectError {}

}

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

impl<S: Display + Debug> Display for SendError<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("SendError: ")?;
        std::fmt::Display::fmt(&self.0, f)
    }
}

impl Display for ConnectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Error connecting")
    }
}
