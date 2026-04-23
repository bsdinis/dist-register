use specs::echo::EchoClient;

use vstd::prelude::*;

verus! {

#[allow(dead_code)]
pub struct TrivialEchoClient<V> {
    _marker: std::marker::PhantomData<V>,
}

impl<C, V> EchoClient<C> for TrivialEchoClient<V> {
    type Val = V;

    type Error = ();

    fn echo(&self, v: Self::Val) -> (r: Result<Self::Val, Self::Error>) {
        Ok(v)
    }
}

} // verus!
