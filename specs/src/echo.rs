use vstd::prelude::*;

verus! {

pub trait EchoError {
    type Val;

    spec fn err_ensures(self, v: Self::Val) -> bool;
}

#[allow(dead_code)]
pub trait EchoClient<C> where  {
    type Error: EchoError<Val = Self::Val>;

    type Val;

    fn echo(&mut self, v: Self::Val) -> (r: Result<Self::Val, Self::Error>)
        ensures
            r is Ok ==> ({
                let r_v = r->Ok_0;
                v == r_v
            }),
            r is Err ==> ({
                let err = r->Err_0;
                err.err_ensures(v)
            }),
    ;
}

} // verus!
