# Campaign 2: legacy give-up records omit the base clock

At mirror b700659, the old absent-zero-key give-up totality is false on its
stated domain. TimerDiscipline.MissingClockFindings proves an explicit witness
for the full expiredRetransmitHandshake callback, with every original premise.

The resident peer has attempts 19, above the limit 18, no zero-key timer, and
an alive peer in a running device. Its valid record input supplies an eight-byte
caller clock of zero and a 24-byte arm record: own clock zero, expiry 135000,
unit address zero. The remaining record list is empty. Both width, exact expiry
and signed clock-gap checks pass. The callback then reaches the actual base-clock
read and returns exactly Stop.hidden for no record left for timer_clk.

The proof runs the imported model symbolically and uses kernel decide only for
concrete arithmetic/validity. It introduces no axiom, compiled evaluation,
readiness premise, reachability claim or state after the error. The mirror is
unchanged. This is a stale theorem-premise finding following the timer-wheel
representation change, not evidence of a kernel bug.

AbsentGiveUpSource and AbsentGiveUpClaims now retain the old domain and prove
exact execution agreement with the actual arm tail, including its failures.
They consume the real caller/guard prefix and preserve the remaining records
and all unrelated Product data. This corrects the old totality claim; it does
not prove that the arm succeeds. RetransmitReadySource/Claims now make the same
correction: actual caller/jitter/guard prefix, inactive success or the actual
active arm outcome, with full Product observations. Other consumers remain pending.

Reproduce with scripts/in-bundle lake build
Leanux.Proofs.WG.TimerDiscipline.MissingClockFindings and scripts/in-bundle
lake env leanchecker --fresh Leanux.Proofs.WG.TimerDiscipline.MissingClockFindings.
Use capped on this host, 32 Lean threads and LEANUX_QEMU_SLOTS=16.
Axiom audit and cumulative counts are in the
[retrofit report](2026-10-16-proof-campaign-2-state-split.md).
