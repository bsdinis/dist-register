use std::collections::HashMap;
use std::collections::HashSet;

use crate::abd::error;
use crate::abd::proto::Request;
use crate::abd::proto::Response;
use crate::abd::proto::Timestamp;
use crate::network::Channel;
use crate::network::connection_pool::ConnectionPool;
use crate::proto::Tagged;

pub trait AbdRegisterClient<C> {
    fn read(&self) -> Result<(Option<u64>, Timestamp), error::Error>;
    fn write(&self, val: Option<u64>) -> Result<(), error::Error>;
}

impl<Pool, C> AbdRegisterClient<C> for Pool
where
    Pool: ConnectionPool<C>,
    C: Channel<R = Tagged<Response>, S = Tagged<Request>>,
{
    fn read(&self) -> Result<(Option<u64>, Timestamp), error::Error> {
        self.shuffle_faults();
        tracing::info!(client_id = self.id(), "reading: first round");
        let request = Tagged::tag(Request::Get);
        let request_tag = request.tag;
        self.broadcast(request);

        let mut still_available = self.n_nodes();
        let mut replies = HashMap::new();
        let mut failed = HashSet::new();

        let mut max_ts = Default::default();
        let mut max_val = None;
        while replies.len() < self.quorum_size() && still_available - failed.len() > 0 {
            for (idx, response) in self.poll(request_tag) {
                match response {
                    Ok(r) => match r.as_deref() {
                        Some(Response::Get { val, timestamp }) => {
                            still_available -= 1;
                            replies.insert(idx, *timestamp);
                            if *timestamp > max_ts {
                                max_ts = *timestamp;
                                max_val = *val;
                            }
                        }
                        Some(r) => {
                            still_available -= 1;
                            tracing::error!(
                                "got weird response to get request {request_tag} from node #{idx}: {r:?}"
                            );
                        }
                        None => {}
                    },
                    Err(e) => {
                        if !failed.contains(&idx) {
                            failed.insert(idx);
                            tracing::error!(
                                "failed to get response from node #{idx} for request {request_tag}: {e:?}"
                            );
                        }
                    }
                }
            }
        }

        if replies.len() < self.quorum_size() {
            return Err(error::Error::FailedFirstQuorum {
                obtained: replies.len(),
                required: self.quorum_size(),
            });
        }

        tracing::info!(client_id = self.id(), quorum = ?replies, "reading: round one quorum obtained");

        if replies.iter().filter(|(_, ts)| **ts == max_ts).count() >= self.quorum_size() {
            tracing::info!(client_id = self.id(), "reading: unanimous decision");
            return Ok((max_val, max_ts));
        }

        // non-unanimous read: write-back

        let old_n_ok = replies.len();
        let mut n_ok = 0;
        let mut received_response_from: Vec<_> = (0..self.n_nodes())
            .map(|idx| replies.get(&idx) == Some(&max_ts))
            .collect();
        let max_ts_reads = received_response_from.iter().filter(|x| **x).count();

        tracing::info!(
            client_id = self.id(),
            "reading: writing back, got {}/{} aggreement",
            max_ts_reads,
            old_n_ok
        );
        let request = Tagged::tag(Request::Write {
            val: max_val,
            timestamp: max_ts,
        });
        let request_tag = request.tag;
        self.broadcast_filter(request, |idx| replies.get(&idx) != Some(&max_ts));

        while n_ok < self.quorum_size() - max_ts_reads
            && received_response_from.iter().any(|received| !received)
        {
            for (idx, response) in self.poll(request_tag) {
                match response {
                    Ok(r) => match r.as_deref() {
                        Some(Response::Write) => {
                            received_response_from[idx] = true;
                            n_ok += 1;
                        }
                        Some(r) => {
                            received_response_from[idx] = true;
                            tracing::error!(
                                "got weird response to get request from node #{idx}: {r:?}"
                            );
                        }
                        None => {}
                    },
                    Err(e) => {
                        if !received_response_from[idx] {
                            received_response_from[idx] = true;
                            tracing::error!(
                                "failed to get response from node #{idx} for request {request_tag}: {e:?}"
                            );
                        }
                    }
                }
            }
        }

        if n_ok + max_ts_reads >= self.quorum_size() {
            let quorum = received_response_from
                .iter()
                .enumerate()
                .filter_map(|(idx, recv)| recv.then_some(idx))
                .collect::<HashSet<usize>>();
            tracing::info!(
                client_id = self.id(),
                ?quorum,
                "reading: round two quorum obtained"
            );
            Ok((max_val, max_ts))
        } else {
            Err(error::Error::FailedSecondQuorum {
                obtained: n_ok + max_ts_reads,
                required: self.quorum_size(),
            })
        }
    }

    fn write(&self, val: Option<u64>) -> Result<(), error::Error> {
        self.shuffle_faults();
        tracing::info!(client_id = self.id(), ?val, "writing: read timestamp phase");
        let request = Tagged::tag(Request::GetTimestamp);
        let request_tag = request.tag;
        self.broadcast(request);

        let mut n_ok = 0;
        let mut received_response_from: Vec<_> = (0..self.n_nodes()).map(|_| false).collect();
        let mut max_ts = Default::default();
        while n_ok < self.quorum_size() && received_response_from.iter().any(|received| !received) {
            for (idx, response) in self.poll(request_tag) {
                match response {
                    Ok(r) => match r.as_deref() {
                        Some(Response::GetTimestamp { timestamp }) => {
                            n_ok += 1;
                            received_response_from[idx] = true;
                            if *timestamp > max_ts {
                                max_ts = *timestamp;
                            }
                        }
                        Some(r) => {
                            received_response_from[idx] = true;
                            tracing::error!(
                                "got weird response to get request from node #{idx}: {r:?}"
                            );
                        }
                        None => {}
                    },
                    Err(e) => {
                        if !received_response_from[idx] {
                            received_response_from[idx] = true;
                            tracing::error!(
                                "failed to get response from node #{idx} for request {request_tag}: {e:?}"
                            );
                        }
                    }
                }
            }
        }

        if n_ok < self.quorum_size() {
            return Err(error::Error::FailedFirstQuorum {
                obtained: n_ok,
                required: self.quorum_size(),
            });
        }
        let quorum = received_response_from
            .iter()
            .enumerate()
            .filter_map(|(idx, recv)| recv.then_some(idx))
            .collect::<HashSet<usize>>();
        tracing::info!(
            client_id = self.id(),
            ?quorum,
            ?max_ts,
            "writing: received quorum for read phase"
        );

        tracing::info!(client_id = self.id(), "writing: write phase");
        let request = Tagged::tag(Request::Write {
            val,
            timestamp: Timestamp {
                seqno: max_ts.seqno + 1,
                client_id: self.id(),
            },
        });
        let request_tag = request.tag;
        self.broadcast(request);

        let mut n_ok = 0;
        let mut received_response_from: Vec<_> = (0..self.n_nodes()).map(|_| false).collect();
        while n_ok < self.quorum_size() && received_response_from.iter().any(|received| !received) {
            for (idx, response) in self.poll(request_tag) {
                match response {
                    Ok(r) => match r.as_deref() {
                        Some(Response::Write) => {
                            received_response_from[idx] = true;
                            n_ok += 1;
                        }
                        Some(r) => {
                            received_response_from[idx] = true;
                            tracing::error!(
                                "got weird response to get request from node #{idx}: {r:?}"
                            );
                        }
                        None => {}
                    },
                    Err(e) => {
                        if !received_response_from[idx] {
                            received_response_from[idx] = true;
                            tracing::error!(
                                "failed to get response from node #{idx} for request {request_tag}: {e:?}"
                            );
                        }
                    }
                }
            }
        }

        if n_ok >= self.quorum_size() {
            let quorum = received_response_from
                .iter()
                .enumerate()
                .filter_map(|(idx, recv)| recv.then_some(idx))
                .collect::<HashSet<usize>>();
            tracing::info!(
                client_id = self.id(),
                ?quorum,
                "writing: received quorum for write phase"
            );
            Ok(())
        } else {
            Err(error::Error::FailedSecondQuorum {
                obtained: n_ok,
                required: self.quorum_size(),
            })
        }
    }
}
