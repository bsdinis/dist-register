# 0004: 2025-12-26 07:27:30

- closed up LinearizationQueue

probable regression -- maybe leaning more on lemmas would be good

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  4463 ms |
|                         total (cpu) |                                 10414 ms |
|           verification (wall-clock) |                                  2669 ms |
|                  verification (cpu) |                                  7263 ms |
|                       smt run (cpu) |                                  2000 ms |
|          abd::invariants::lin_queue |                                  1212 ms |
|                         abd::client |                                  1026 ms |
|             abd::invariants::quorum |                                   488 ms |
|       abd::invariants::committed_to |                                   427 ms |
|                                     |                                   416 ms |
|                 ellapsed wall clock |                               0:04.98    |

---

# 0003: 2025-12-25 21:49:39

- closed up Pending and Committed

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  3099 ms |
|                         total (cpu) |                                  8641 ms |
|           verification (wall-clock) |                                  1990 ms |
|                  verification (cpu) |                                  6706 ms |
|                       smt run (cpu) |                                  1824 ms |
|                         abd::client |                                  1088 ms |
|          abd::invariants::lin_queue |                                   877 ms |
|             abd::invariants::quorum |                                   447 ms |
|                                     |                                   412 ms |
|       abd::invariants::committed_to |                                   380 ms |
|                 ellapsed wall clock |                               0:05.44    |

---

# 0002: 2025-12-24 22:11:08

- closed up committed to

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  3214 ms |
|                         total (cpu) |                                  8822 ms |
|           verification (wall-clock) |                                  2098 ms |
|                  verification (cpu) |                                  6870 ms |
|                       smt run (cpu) |                                  1890 ms |
|                         abd::client |                                  1176 ms |
|          abd::invariants::lin_queue |                                   944 ms |
|             abd::invariants::quorum |                                   453 ms |
|                                     |                                   428 ms |
|       abd::invariants::committed_to |                                   394 ms |
|                  elapsed wall clock |                               0:04.15    |

---

# 0001: 2025-12-24 22:11:08

- initial benchmarking

|                                     |                                          |
|---|---|
|                             profile |                               release    |
|                             version |            0.2025.12.22.95ec04c.dirty    |
|                            platform |                          linux_x86_64    |
|                           toolchain |       1.91.0-x86_64-unknown-linux-gnu    |
|                        verus commit | 95ec04c1198741329100b84cae4c3b49916b1c52 |
|                            hostname |                                bertha    |
|                           n_threads |                                    15    |
|                  total (wall-clock) |                                  3298 ms |
|                         total (cpu) |                                  8936 ms |
|           verification (wall-clock) |                                  2207 ms |
|                  verification (cpu) |                                  7038 ms |
|                       smt run (cpu) |                                  2104 ms |
|                         abd::client |                                  1339 ms |
|          abd::invariants::lin_queue |                                   995 ms |
|             abd::invariants::quorum |                                   444 ms |
|                                     |                                   421 ms |
|       abd::invariants::committed_to |                                   351 ms |
|                  elapsed wall clock |                               0:04.15    |
