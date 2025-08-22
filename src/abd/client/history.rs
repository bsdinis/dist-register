use vstd::prelude::*;

verus! {

    /*
pub enum HistEntry {
    Write {
        val: Option<u64>,
    },
    Read {
        val: Option<u64>,
    }
}

pub struct History {
    prefix: Seq<HistEntry>
}

impl History {
    pub open spec fn contains_read(self, val: Option<u64>) -> bool {
        self.prefix.contains(HistEntry::Read { val })
    }

    pub open spec fn last_write_val(self) -> Option<u64> {
        self.prefix.filter_map(|entry| match entry {
            HistEntry::Read { .. } => None,
            HistEntry::Write { val } => Some(val),
        }).last()
    }
}
    */

}
