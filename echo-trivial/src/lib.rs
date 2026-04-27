use vstd::prelude::*;

verus! {

#[allow(dead_code)]
pub struct TrivialEchoClient<V> {
    _marker: std::marker::PhantomData<V>,
}

pub struct TrivialError<V> {
    _marker: std::marker::PhantomData<V>,
}

impl<V> specs::echo::EchoError for TrivialError<V> {
    type Val = V;

    open spec fn err_ensures(self, val: Self::Val) -> bool {
        true
    }
}

impl<C, V> specs::echo::EchoClient<C> for TrivialEchoClient<V> {
    type Val = V;

    type Error = TrivialError<V>;

    fn echo(&mut self, v: Self::Val) -> (r: Result<Self::Val, Self::Error>) {
        Ok(v)
    }
}

} // verus!
