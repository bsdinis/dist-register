use vstd::prelude::*;

verus! {

#[allow(dead_code)]
pub trait EchoClient<C> where  {
    type Error;

    type Val;

    fn echo(&self, v: Self::Val) -> (r: Result<Self::Val, Self::Error>)
        ensures
            r is Ok ==> ({
                let r_v = r->Ok_0;
                v == r_v
            }),
    ;
}

} // verus!
