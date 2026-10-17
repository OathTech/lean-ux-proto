# Campaign 2 timer carry: stale exact-peer statements

The state-split retrofit at mirror `b700659` exposes a statement artefact in
H6's pre-wheel exact-peer postconditions. The mirror's timer deletion clears
both the expiry and the corresponding wheel entry. The former
`delTimer_exact` conclusion describes only the expiry update and therefore
incorrectly preserves a new wheel field.

The current carry corrects `armTimer_recorded` and `delTimer_exact` in
`ArmingClaims`, using only the campaign projection. Recorded arming now
specifies the complete WG state, with separate same-expiry and changed-expiry
effects; deletion specifies the complete native snapshot with both timer
fields cleared. Their original normal-return domains are retained. The guarded arming and
session-derived callers are now corrected in GuardedArmingClaims, with separate
TimerInputFrames establishing input mode and guard facts. ArmingLifecycleClaims
now carries traversal, data receipt and handshake completion; all seven identified
contracts are corrected. Their downstream consumers remain pending. These are explicit statement
corrections, not type-only carries; the former deletion statement remains
refuted by the witness below.

`Leanux/Proofs/WG/TimerDiscipline/ArmingWheelFindings.lean` proves
`delTimer_legacy_exact_counterexample` with the Lean kernel. For every Ambient
input it constructs a resident peer at identifier 0 with:

- send-keepalive expiry `some 1`;
- wheel entry `some ⟨2, 2, 1⟩` (slot, bucket expiry, enqueue stamp);
- no pending/slotted inconsistency according to `TimerWheel.peerWheelProblem`.

The actual `delTimer 0 .sendKeepalive` returns normally, leaves Ambient
unchanged, and yields a peer unequal to `p.setTimer .sendKeepalive none`.
Projection of `wheelSendKeepalive` distinguishes them: the actual operation
clears it; the old conclusion keeps the entry. The exact current update is
`(p.setTimer timer none).setWheel timer none` in `Leanux/WG/State.lean`.

The original contract universally quantified all resident peers. This witness
falls within that domain. Its local pending/slotted consistency does not
establish global reachability: the fixture does not populate `peerList` or
align the world's enqueue counter with the chosen stamp. No reachable-state
or kernel-behavior claim follows from this counterexample.

Source inspection identifies seven affected contracts in `ArmingSource`:
`armTimer_recorded`, `delTimer_exact`, `modPeerTimer_effect`,
`timersTraversal_effect`, `timersSessionDerived_effect`,
`timersDataReceived_effect` and `timersHandshakeComplete_effect`. Arming's
full-peer update now includes wheel placement and its counter; cancellation
clears the wheel entry. Only the deletion counterexample above has been
checked as a concrete witness in this tranche. Recorded arming additionally
observes fields split between Ambient and WG, so its native claim must retain
both components through the campaign projection.

[AGENT 2026-10-17] Keep those seven legacy contracts pending, retain their
source bodies, and carry their timer behavior through explicit current wheel
effects. Do not silently discard the new state from exact equalities or
delete these substantive within-WireGuard claims. The evidence classifies
the failure as a stale statement after a representation change; no mirror
repair is requested.

The unaffected result-map rule and guard contract are carried separately in
`ArmingBaseSource`. The original generic product map domain remains, with a
separate native companion for `StateT σ AmbientM`.

Validation: scoped capped build of `ArmingBaseSource` and
`ArmingWheelFindings` passed 29 jobs without warnings. Axiom inspection of
the closure's 16 logical roots found only `propext`, `Classical.choice` and
`Quot.sound`. Fresh replay is recorded in the
[retrofit report](2026-10-16-proof-campaign-2-state-split.md).

Reproduce with `scripts/in-bundle lake build
Leanux.Proofs.WG.TimerDiscipline.ArmingBaseSource
Leanux.Proofs.WG.TimerDiscipline.ArmingWheelFindings`, then
`scripts/in-bundle lake env leanchecker --fresh
Leanux.Proofs.WG.TimerDiscipline.ArmingWheelFindings`; use `capped --` on the
shared host. That checkpoint did not validate the seven legacy contracts or the full H6
terminal closure.

The next retrofit tranche adds two separately named contracts in
`ArmingWheelSource`: `delTimer_wheel_exact` and
`timersHandshakeComplete_wheel_effect`. Both keep the original resident-peer
and normal-return scope and state the complete current peer update, including
the selected wheel clear. Handshake completion also resets attempts and the
last-minute flag and records the actual hidden clock bytes. At that companion checkpoint all seven legacy
contracts remained pending; these companions do not invalidate the counterexample
or establish reachability. The scoped build passes 32 jobs without warnings;
axiom inspection and fresh replay are recorded in the retrofit report.

The later projected correction retains the finding and checks `ArmingClaims`
with a scoped build, standard-axiom inspection and fresh replay; counts and
commands are in the retrofit report. The complete H6 terminal closure remains
lagging while downstream timer and worker consumers are carried.
