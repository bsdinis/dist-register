#[allow(unused_imports)]
use builtin::*;
use vstd::prelude::*;

verus! {

ghost enum HistEntry {
    Write {
        val: Option<u64>,
    },
    Read {
        val: Option<u64>,
    }
}

ghost struct History {
    entries: Seq<HistEntry>
}

}
