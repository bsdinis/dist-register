use vstd::prelude::*;

mod echo;
mod request;
mod response;

pub use echo::*;
pub use request::*;
pub use response::*;

verus! {

pub enum ReqType {
    Echo,
}

} // verus!
