use abd::timestamp::Timestamp;
use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn report_quorum_size(quorum_size: usize) {
    println!("quorum size: {quorum_size}");
}

#[verifier::external_body]
#[allow(unused)]
pub fn report_read(client_id: u64, r: (Option<u64>, Timestamp)) {
    eprintln!(
        "client {client_id:3} read finished: {:20}",
        format!("{r:?}")
    );
}

#[verifier::external_body]
#[allow(unused)]
pub fn report_err<E: std::error::Error>(client_id: u64, e: &E) {
    eprintln!("client {client_id:3} failed: {e:20?}");
}

#[verifier::external_body]
#[allow(unused)]
pub fn report_write(client_id: u64, value: Option<u64>) {
    eprintln!(
        "client {client_id:3} write finished: {:20}",
        format!("{value:?}")
    );
}

} // verus!
