#![allow(dead_code)]

use std::collections::BTreeSet;
use std::collections::HashMap;

#[derive(Debug)]
enum Operation {
    Read(Option<u64>),
    Write(Option<u64>),
}

struct Event {
    event_id: u64,
    begin_ms: u64,
    end_ms: u64,
    op: Operation,
}

type Trace = Vec<Event>;

struct PartialOrder(HashMap<(u64, u64), bool>);
impl std::ops::Deref for PartialOrder {
    type Target = HashMap<(u64, u64), bool>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
struct ConcisePartialOrder(HashMap<u64, BTreeSet<u64>>);
impl std::ops::Deref for ConcisePartialOrder {
    type Target = HashMap<u64, BTreeSet<u64>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<&PartialOrder> for ConcisePartialOrder {
    fn from(value: &PartialOrder) -> Self {
        let mut lt_order: HashMap<u64, BTreeSet<u64>> = HashMap::new();
        for ((k, v), lt) in &**value {
            if *lt {
                lt_order.entry(*k).or_default().insert(*v);
            }
        }

        // remove transitives
        loop {
            let mut removed = false;

            let mut removals = vec![];
            for (k, greaters) in &lt_order {
                let rem: Vec<_> = greaters
                    .iter()
                    .filter(|a| {
                        greaters
                            .iter()
                            .any(|b| lt_order.get(b).map(|v| v.contains(a)).unwrap_or(false))
                    })
                    .copied()
                    .collect();

                if !rem.is_empty() {
                    removals.push((*k, rem));
                    removed = true;
                }
            }

            for (k, rems) in removals {
                for r in rems {
                    lt_order.entry(k).and_modify(|x| {
                        x.remove(&r);
                    });
                }
            }

            if !removed {
                break;
            }
        }

        ConcisePartialOrder(lt_order)
    }
}

impl std::fmt::Debug for ConcisePartialOrder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, v) in &**self {
            writeln!(f, "{k:3} < {v:3?}")?;
        }

        Ok(())
    }
}

impl std::fmt::Debug for PartialOrder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let concise: ConcisePartialOrder = self.into();
        concise.fmt(f)
    }
}

fn realtime(trace: &[Event]) -> PartialOrder {
    let mut order = HashMap::new();
    for op1 in trace {
        assert!(op1.begin_ms < op1.end_ms, "invalid event");
        for op2 in trace {
            if op1.end_ms < op2.begin_ms {
                order.insert((op1.event_id, op2.event_id), true);
            } else if op2.end_ms < op1.begin_ms {
                order.insert((op1.event_id, op2.event_id), false);
            }
        }
    }

    PartialOrder(order)
}

fn partial(trace: &[Event]) -> PartialOrder {
    let mut order = HashMap::new();

    for op1 in trace {
        assert!(op1.begin_ms < op1.end_ms, "invalid event");
        for op2 in trace {
            if let (Operation::Read(read_v), Operation::Write(write_v)) = (&op1.op, &op2.op) {
                if read_v == write_v {
                    order.insert((op1.event_id, op2.event_id), false);
                    order.insert((op2.event_id, op1.event_id), true);
                }
            }
        }
    }

    PartialOrder(order)
}

fn orders_agree(o1: &PartialOrder, o2: &PartialOrder) -> bool {
    for (k, lt1) in &**o1 {
        if o2.get(k) == Some(&!lt1) {
            return false;
        }
    }

    for (k, lt2) in &**o2 {
        if o1.get(k) == Some(&!lt2) {
            return false;
        }
    }

    true
}
