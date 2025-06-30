#[allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;

verus! {

#[allow(dead_code)]
ghost enum HistEntry {
    Write {
        val: Option<u64>,
    },
    Read {
        val: Option<u64>,
    }
}

#[allow(dead_code)]
ghost struct History {
    entries: Seq<HistEntry>
}

}
