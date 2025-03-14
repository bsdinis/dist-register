#[derive(Clone, Default, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp {
    pub seqno: u64,
    pub client_id: u64,
}

impl std::fmt::Debug for Timestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.seqno.fmt(f)?;
        f.write_str(".")?;
        self.client_id.fmt(f)
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
