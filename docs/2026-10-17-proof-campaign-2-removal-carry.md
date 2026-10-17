# Campaign 2 removal carry: stale totality domain

At mirror b700659, the old quiet and live peer-removal return contracts
omit a crypt-work guard that landed in a7a5e1f. The actual
Leanux/WG/PeerRemove.lean peerRemoveAfterDead clears keypairs and timers,
then rejects pending encrypt, decrypt or transmit work or any scheduled
NAPI poll, before draining handshake work, decrementing the peer count and
releasing the reference. This is an explicit modeled-domain boundary
already documented by the peer audit, not a newly discovered mirror defect.

QuietRemovalSource restores that guard in the original source equation.
QuietRemovalFindings proves
peerRemoveAfterDead_legacy_total_napi_counterexample for every Ambient input.
Its concrete mathematical state has a resident dead peer at identifier 0,
reference count 2, a positive device peer count, empty keypair slots, empty
send/clear work queues, and napiScheduled=true. ClearReady also holds.

The proof composes the actual empty-keypair clearing and timer-cleanup
contracts. After their real successor states, the scheduled poll remains
in the peer map and the actual guard stops with outsideDomain and its
crypt-work message. The diagnostic site is the real post-prefix decision-log
site, existentially retained. No post-error state is asserted.

The witness negates total return even with postcondition True under the old
resident-device precondition. It therefore refutes both old quiet and live
after-death totality conclusions on their stated domains. It does not
establish reachability, coherent peer-list membership or kernel behavior.
At this finding checkpoint the broader removal callers remained pending;
they were not silently given extra readiness assumptions.

[AGENT 2026-10-17] Classify the failed totality as statement lag following the
landed guard. Retain the pending contracts and report the counterexample;
no mirror change is requested.

The independent source factor and finding build cleanly. Scoped axiom
inspection and fresh replay, with cumulative counts and all failed proof
attempts, are recorded in the
[retrofit report](2026-10-16-proof-campaign-2-state-split.md).
Reproduce with scripts/in-bundle lake build
Leanux.Proofs.WG.Config.QuietRemovalFindings, then
scripts/in-bundle lake env leanchecker --fresh
Leanux.Proofs.WG.Config.QuietRemovalFindings. Use capped on this host.
The full H4 terminal closure subsequently passed scoped build, standard-axiom
inspection and fresh replay. The aggregate gate still fails in inherited
CounterWindow/ReplayWindow files.

The two quiet-removal contracts now classify exact refusal or the original
successful cleanup effect on the same premises, including the actual outer
removal prefix. Four private exact-prefix helpers retain the actual native
states and decision logs. The three general live-removal source contracts now classify exact outcomes
using actual clear/timer/outer-prefix execution witnesses for diagnostics.
Their terminal projected wrappers are now checked in Config.Statements,
including original_peer_remove_quiet and original_peer_remove_live. Initial-state
REPLACE_PEERS cleanup/ownership transport remains separate and open.
Validation and the complete failed-probe ledger are in the retrofit report.
