use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp {
    pub seqno: u64,
    pub client_id: u64,
}

impl Timestamp {
    pub fn default() -> (r: Self)
        ensures
            r.seqno == 0,
            r.client_id == 0
    {
        Timestamp { seqno: 0, client_id: 0 }
    }

    pub open spec fn to_nat(&self) -> (nat, nat) {
        (self.seqno as nat, self.client_id as nat)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Request {
    Get,
    GetTimestamp,
    Write {
        val: Option<u64>,
        timestamp: Timestamp,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Response {
    Get {
        val: Option<u64>,
        timestamp: Timestamp,
    },
    GetTimestamp {
        timestamp: Timestamp,
    },
    Write,
}

}

impl std::fmt::Debug for Timestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.seqno.fmt(f)?;
        f.write_str(".")?;
        self.client_id.fmt(f)
    }
}
