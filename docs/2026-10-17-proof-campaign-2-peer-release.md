# Campaign 2 peer-release carry: stale totality domain

The retrofit to mirror `b700659` finds that the former `peerPut_exact`
totality statement has insufficient premises for the current mirror. It
requires a resident peer with a positive reference count. Those premises
allow a final release with queued work or a pending timer; the actual
operation stops at its cleanup guards in these cases.

`Leanux/Proofs/WG/Index/PeerReleaseFindings.lean` contains two kernel-checked
counterexamples, each quantified over arbitrary Ambient input:

- `peerPut_legacy_total_queued_counterexample` uses a resident peer at 0,
  reference count 1 and one transmit queue item. The actual native run stops
  at the queued-packet invariant.
- `peerPut_legacy_total_timer_counterexample` uses empty transmit and receive
  queues, reference count 1, send-keepalive expiry `some 1` and wheel entry
  `some ⟨2, 2, 1⟩`. `TimerWheel.peerWheelProblem` reports no local mismatch,
  but the actual native run stops at the pending-timer invariant.

Both prove the exact stopped outcome and negate the old expected-device total
return contract. Neither exposes a post-failure state: `Except.error` carries
none. These are mathematical witnesses in the old statement's universal
domain, not claims about reachable driver states. In particular, they do not
establish global peer-list, enqueue-counter or packet-reference coherence.

The source is `Leanux/WG/Peer.lean`'s `peerPut`: decrement the reference,
test final release, remove the handshake entry through the actual guarded
index adapter, check queues, purge and erase, check pending timers, then
retire dispatch identities. The incoming guards are behavioral changes since
the old mirror pin, not facts supplied by the state split's types.

[AGENT 2026-10-17] Classify this as a statement-domain artefact. Keep the
legacy total contract pending instead of silently adding readiness premises
or deleting a substantive claim. No mirror repair or kernel-behavior claim
is requested. The separate keypair-release contract in `Index/Release`
remains checked on its original domain.

The scoped capped build passed 43 jobs without warnings. Axiom inspection
and fresh kernel replay pass; the full H2 closure is still lagging. See the
[retrofit report](2026-10-16-proof-campaign-2-state-split.md) for combined
counts and validation. Reproduce with `scripts/in-bundle lake build
Leanux.Proofs.WG.Index.PeerReleaseFindings`, then
`scripts/in-bundle lake env leanchecker --fresh
Leanux.Proofs.WG.Index.PeerReleaseFindings`; use `capped --` on the shared host.

The later retrofit explicitly corrects `peerPut_exact` to a projected exact-outcome
contract under the same resident/live hypotheses. On final release, queue
refusal takes precedence over the first pending timer or wheel entry; each
produces its exact invariant Stop. All other cases return the original
releasedPeerDevice. It asserts no post-error state. This preserves the checked
counterexamples and does not add readiness. The two original terminal wrappers
and downstream configuration/timer users still need their own domain carry.
The corrected source passes scoped build, standard-axiom inspection and fresh
replay, recorded in the retrofit report.
