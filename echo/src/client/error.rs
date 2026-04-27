use vstd::prelude::*;

verus! {

/// Echo errors
///
/// The only way an Echo fails is when the network fails
pub struct EchoError;

impl std::error::Error for EchoError {

}

impl specs::echo::EchoError for EchoError {
    type Val = String;

    open spec fn err_ensures(self, message: String) -> bool {
        true
    }
}

} // verus!
impl std::fmt::Debug for EchoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EchoError").finish()
    }
}

impl std::fmt::Display for EchoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EchoError").finish()
    }
}
