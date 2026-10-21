# Lifetime fault-exclusion probe

Baseline: `c63423ef`, including campaign 3's landing `3361fb77`. This is the
first bounded probe queued by the fresh-eyes review, finding 3. The mirror is
unchanged. The proposed initialized claim remains **open**; the local bridge
from R2's invariant is false. No reachable mirror defect is claimed.

## Goal and independent admission

`LifetimeSafety.FaultProbe.ParsedDefaultWireGuard` admits a typed trace when it
is the image of `Runner.parseTrace`, uses the default network fixture, and has
neither a bare/foreign fixture, a stepped dump nor a seccomp child. It places no
success, domain-filter, lifetime, reference-count or scheduling-result premise
on the execution. Hidden records and operations remain unrestricted.

`InitializedFaultExclusion` asks that such a trace, with either placeholder
setting, cannot return an indexed Stop for a missing device, dangling peer or
dangling keypair. Other invariant failures, unsupported paths and record
mismatches remain possible. This is committed execution only: faults discarded
inside speculative schedule trials require a separate attempted-access claim.
The definition is an open proposition, not an exported theorem.
Even closing it would not establish every form of C dereference safety:
`IndexOwner.peerDeref` reports a NULL peer word as an unsupported path, outside
this invariant-fault predicate. Excluding that arm and relating logical IDs
to C pointers/RCU lifetime are additional obligations.

## Attempt and obstruction

The attempted route was to strengthen R2's initialized composition with an
error postcondition excluding lookup faults. At the getter contract this needs
the supplied identifier to resolve, before the getter returns. R2's
`AllocationInv` supplies fresh allocation bounds, resident identity uniqueness,
and absence of released identities. It does not connect stored references to
those residents. Its `getPeerPrefix` and `getKeypairPrefix` retain history
unchanged when the getter fails.

The checked local countermodel `staleWorld` has one resident peer (slot 0,
allocation 1), an empty keypair store, a public-key table entry pointing to
missing peer 7, and the resident peer's next-key slot pointing to missing
keypair 7. It satisfies **all of `AllocationInv []`**, yet the original
`pubkeyLookup []` stops with `dangling peer 7` and the original
`keypairsClear 0` stops with `dangling keypair 7`.

This is a countermodel to the proposed invariant-to-error-exclusion step. It
is deliberately not presented as an initialized trace, a counterexample to
R2, or evidence of a Linux fault. The initialized goal cannot be disproved by
constructing an arbitrary inconsistent world.

Campaign 3 contains useful stronger ingredients: `Credits.Exact.resident`
derives key residency from an actual funded occurrence; `HolderBoundary.Entry`
combines key holders, peer funding and slot liveness; and
`HolderInitialized.account` derives exact key accounting at normal initialized
endpoints. These rule out relevant bad boundary states. They do **not** already
prove the proposed error postcondition: `hoare_iff_run_ambient` explicitly
characterizes the underlying `Hoare` contracts by normal returns only. An
invariant fault before that return satisfies such a partial contract.

## Cost and stop point

The blocker is a missing proof, not a resource limit or a detected mirror bug.
The next proof needs reference validity at every reached call entry, including
detached locals during get/publish and detach/put intervals, followed by
composition with a nontrivial exceptional postcondition. Preserve the existing
normal-boundary funding results as inputs; do not assume a successful overall
run to obtain them. Peer registries, index owners, the three key slots, packets,
workers, timers and teardown all contribute identifiers. The WG sources contain
145 lines mentioning `getPeer` and 18 mentioning `getKeypair` (a rough source
inventory, not a count of distinct runtime sites).

**Estimate [AGENT 2026-10-21]:** two to four focused weeks for this initialized
class, with high uncertainty in scheduler and teardown composition. A first
two-day milestone should close error-aware public-key lookup and key-slot
clearing under the existing funded entry packages, then demonstrate transport
to an actual initialized call entry. If that transport is still absent, stop
and revise the estimate. No additional weaker result catalogue is proposed.
This probe stops at the concrete obstruction and cost report; it does not
silently narrow the initialized goal to a primitive call or a successful run.

## Claims kept distinct

| Claim | Present evidence and boundary |
| --- | --- |
| Successful lookup-history safety | R2's `runner_initialized_access_safety`, including safe reached histories on Stop. |
| No invalid peer/keypair dereference attempt | The initialized fault-exclusion goal above is open. Missing lookups stop noisily; absence of such stops is not established. Logical store resolution is not a C pointer/RCU simulation. |
| Reference accounting | C3's `initialized_exact_key_reference_account` / `accepted_exact_key_reference_account` cover normal initialized endpoints and actual durable holders. Source-local obligations remain relevant inside calls. |
| Eventual reclamation | Payment of a final reference can establish removal. Neither accounting nor this probe establishes that all references will eventually be paid, a scheduling fairness theorem, or C RCU grace-period completion. |

## Reproduction

From the repository root with the declared Lean toolchain:

```sh
lake build Leanux.Proofs.WG.LifetimeSafety.FaultProbe
lake env lean Leanux/Proofs/WG/LifetimeSafety/FaultProbe.lean
```

On the shared box, prefix builds/checks with `capped -- scripts/in-bundle`.
The focused build passed (117 jobs, no warnings). `#print axioms` on
`allocation_invariant_does_not_exclude_lookup_faults` reports only `propext`,
`Classical.choice` and `Quot.sound`. No resource limit was raised. The module is
imported by the proof root so the normal full gate includes its declarations.
Final branch validation is recorded in the probes' closing report.
