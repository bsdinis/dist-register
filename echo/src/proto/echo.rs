use vstd::prelude::*;

verus! {

pub struct EchoRequest {
    #[allow(unused)]
    message: String,
}

#[allow(unused)]
pub struct EchoResponse {
    message: String,
}

#[allow(unused)]
impl EchoRequest {
    pub fn new(message: String) -> (r: Self)
        ensures
            r.spec_message() == message,
    {
        EchoRequest { message }
    }

    pub closed spec fn spec_message(self) -> String {
        self.message
    }

    pub fn message(self) -> String
        returns
            self.spec_message(),
    {
        self.message
    }

    pub closed spec fn spec_eq(self, other: Self) -> bool {
        self.spec_message() == other.spec_message()
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
    }

    pub broadcast proof fn lemma_spec_eq(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            a.spec_message() == b.spec_message(),
    {
    }
}

#[allow(unused)]
impl EchoResponse {
    pub fn new(message: String) -> (r: Self)
        ensures
            r.spec_message() == message,
    {
        EchoResponse { message }
    }

    pub closed spec fn spec_message(self) -> String {
        self.message
    }

    pub fn message(self) -> String
        returns
            self.spec_message(),
    {
        self.message
    }
}

impl EchoResponse {
    pub closed spec fn spec_eq(self, other: Self) -> bool {
        self.spec_message() == other.spec_message()
    }

    pub broadcast proof fn spec_eq_refl(a: Self)
        ensures
            #[trigger] a.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_symm(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            b.spec_eq(a),
    {
    }

    pub broadcast proof fn spec_eq_trans(a: Self, b: Self, c: Self)
        requires
            #[trigger] a.spec_eq(b),
            #[trigger] b.spec_eq(c),
        ensures
            a.spec_eq(c),
    {
    }

    pub broadcast proof fn lemma_spec_eq(a: Self, b: Self)
        requires
            #[trigger] a.spec_eq(b),
        ensures
            a.spec_message() == b.spec_message(),
    {
    }
}

impl Clone for EchoRequest {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        EchoRequest { message: self.message.clone() }
    }
}

impl Clone for EchoResponse {
    fn clone(&self) -> (r: Self)
        ensures
            self.spec_eq(r),
            r.spec_eq(*self),
    {
        EchoResponse { message: self.message.clone() }
    }
}

} // verus!
impl std::fmt::Debug for EchoRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EchoRequest")
            .field("message", &self.message)
            .finish()
    }
}

impl std::fmt::Debug for EchoResponse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EchoResponse")
            .field("message", &self.message)
            .finish()
    }
}
