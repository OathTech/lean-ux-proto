# C1: the two open propositions

2026-11-10, branch `task/binary-c1` after the integration of the four
packages. `binary/C1Signed.lean` proves

    theorem signed_of_referenced_and_witness : ReferencedHolds → WitnessHolds → Signed

with every other interface proposition discharged by a package's theorem
(the `example`s in that file list them). Two propositions of
`binary/C1Interfaces.lean` are unproved. Each has one prover, one file
prefix and one acceptance theorem. Nothing else is open. [AGENT 2026-11-10,
integrator]

Rules for both: work on a branch cut from the integrated head; no change to
the statement files (`binary/StatementC1*.lean`), to `C1Interfaces.lean`,
`C1Invariant.lean`, `C1Step.lean`, `C1Cut.lean`, `C1Assembly.lean`,
`C1Signed.lean` or to another package's modules. If a proposition cannot be
proved as stated, stop and report it with the failing step; do not restate
it. No `sorry`, `axiom`, `native_decide`, `unsafe`, resource raise or
warning suppression. New modules are listed as roots in
`binary/lakefile.toml` (the library names its roots one by one) and
imported by the prover's root.

## 1. `ReferencedHolds` (prefix `C1Referenced`, root `binary/C1Referenced.lean`)

The proposition:

```lean
def ReferencedHolds : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    Referenced L (Inv L A)
```

with, from `StatementC1Headline.lean` (revision 4),

```lean
def CountMoved (L : Layout) (pid : PeerId) (before after : Nat) (m m' : Mem 64) : Prop :=
  ∃ peer, Trie.address L.peers (some pid) = .ok peer ∧
    readNat ⟨{dmem := m},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok before ∧
    readNat ⟨{dmem := m'},0⟩ (peer+Root.nodeOffsets.peerRefcount) 4 = .ok after ∧
    ∀ a, L.Heap a → ¬InRange (.ofNat 64 (peer+Root.nodeOffsets.peerRefcount)) 4 a → m.get? a = m'.get? a

def Referenced (L : Layout) (Inv : World → Mem 64 → Prop) : Prop :=
  ∀ (w w' : World) (m m' : Mem 64) (pid : PeerId) (count : Nat), Inv w m →
    ((liftWG (WG.peerGetMaybeZero (some pid))).run w = .ok (some pid, w') ∧
      CountMoved L pid count (count+1) m m') ∨
    ((liftWG (WG.peerPut (some pid))).run w = .ok ((), w') ∧ 1 < count ∧
      CountMoved L pid count (count-1) m m') →
    Inv w' m'
```

and `Inv` the `Related` of `C1Invariant.lean`. The take is the mirror's
`peerGetMaybeZero` returning the peer (not `peerGet`); the drop is a
`peerPut` from a count above one.

What it can use on the integrated branch:

- Package 1's `binary/C1Source.lean` (imported by the root). `framedHolds`
  and its lemma `related_frame` are the model: `Inv` across a memory change
  that leaves the reconstruction's reads alone. `initialHolds`'s
  `emptyTable_facts` and the span lemmas (`readSpans_heap`,
  `metadataSpans_subset`, `count_fixed`, `count_objects`,
  `readSpans_within`) place the count word. `lookupHolds` is the nearest
  finished proof: it carries `Inv` across the one count the compiled lookup
  raises, and its `frames_peerGet_pending`, `frames_lookup_pending` and
  `lookup_pending` show that the mirror's lookup leaves the pending records
  and the armed sites alone; the same is needed here for
  `peerGetMaybeZero` and `peerPut` taken alone.
- The landed count lemmas: `target_mapCounts` (`PairAllowedipsCount.lean`:
  the target of a device with one peer's `refcount` replaced is
  `mapCounts` of the old target) and `heap_mapCounts`
  (`PairAllowedipsHeapFrame.lean`: `heap` does not read the counts).
- How the landed `lookup_checked` (`PairAllowedipsLookupAdequacy.lean`)
  treats `peerGetMaybeZero`: `Trie.lookup_effect` gives the mirror's device
  after a hit as the old one with the found peer's `refcount` plus one; the
  relation is carried by `reconstruct_hit` and the shape by the rewrite
  `target_mapCounts … ; heap_mapCounts`. The take here is that same mirror
  operation without the walk around it, so the same three steps apply once
  the reconstruction's count read is matched to `CountMoved`.
- The count word lies in a peer, apart from the arena (a conjunct of
  `Inv`), so `A.Idle` survives by the contract's `frame` clause
  (`premises.allocator`), as in `related_frame`.

Acceptance: `theorem referencedHolds : ReferencedHolds` in
`binary/C1Referenced.lean`, namespace `Binary.Statements.C1.Proof`, with
`#print axioms referencedHolds` showing only `propext`, `Classical.choice`,
`Quot.sound`; `lake -d binary build` and `scripts/binary-proof-gate` pass.

## 2. `WitnessHolds` (prefix `C1Witness`, root `binary/C1Witness.lean`)

The proposition:

```lean
def WitnessHolds : Prop := HeadlineFor → Witness

def Witness : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator),
    Premises fetch L A ∧ CallbacksFromImage fetch ∧ Executed fetch L A ∧ ServiceActive fetch L A
```

`Executed` and `ServiceActive` are in `StatementC1Vacuity.lean` (revision
3): the four calls of an actual execution from an empty table (root
insertion; an insertion allocating twice with the coverage buffer in use;
an insertion whose second allocation is refused; a lookup that finds a
peer), each given by `Ran` between its entry and final states; and one
admissible entry state of the code at `allocEntry` from which an actual
execution returns having changed a byte of its scratch and a byte of the
coverage buffer, with `0 < A.depth`.

The root imports `C1Signed`, so `headlineFor : HeadlineFor` (closed, no
hypothesis) is available; the acceptance theorem still takes `HeadlineFor`
as its hypothesis, as the interface states it.

What it can use:

- `binary/C1ServiceStub*.lean`: the package's stub (`Stub.allocCode`,
  `Stub.freeCode`, `Stub.fetch`, `Stub.layout`, `Stub.allocator`,
  `Stub.Idle`), its runs (`Stub.alloc_run`, `Stub.free_run` in
  `C1ServiceStubRun.lean`), `Stub.idle_initial`
  (`C1ServiceStubIdle.lean`), and `Stub.contract`
  (`C1ServiceStubContract.lean`): the stub's code meets
  `AllocatorContract` of revision 4. This stub is quiet: it does not use
  its stack and does not write the coverage buffer, so it meets
  `PremisesMet` (`premisesMet`) but not `ServiceActive`.
- `premises_of_contract` (`C1ServiceCallbackPremises.lean`): `Premises`
  and `CallbacksFromImage` for the joint decoder `Joint.fetch stub` from
  `Joint.Within stub Joint.stubLow Joint.stubHigh` and the stub's
  `AllocatorContract`. A new stub goes through this unchanged provided its
  code stays inside the stub's address range (`C1ServiceJointFetch.lean`).
- `ran_of_eventually` (`C1ServiceHistory.lean`): an `Eventually` whose
  postcondition gives `Returned` yields `Ran` and the postcondition at the
  final state. With `HeadlineFor` at the witness's own `fetch` this is
  `Executed`: `InsertStep` and `LookupStep` give each call's `Eventually`;
  `Framed` and `HeapSame` carry `Inv` from one call's final state to the
  next entry state, whose bytes outside the heap are the prover's to
  choose; the mirror's four runs are concrete evaluations.
- `Statements/C1/proof/StateWord.lean` (a regression file outside the
  library; its proofs use the statement files only and can be restated in
  the prover's modules): `mode_apart` (an admitted context's bytes are not
  in the arena or the service's stack) and `metadata_kept` (whatever a
  conforming service writes, the context's metadata and the preemption
  count are unchanged). Under revision 3's `ServiceReady.separated` these
  are why a stub may change a scratch byte and append to the coverage
  buffer and still give `c.At` after the call.
- The statement author's note (`docs/2026-11-10-c1-final-statement.md`,
  the section on the witness): one workable design is a stub that calls
  the image's own `__sanitizer_cov_trace_pc`, whose landed contract
  already gives the write frame and `c.At`. That a stub does satisfy
  `ServiceActive` is not proved anywhere yet. The executable test service
  of `Statements/C1/Test.lean` is an instance on which `ServiceActive`
  evaluates true, and the quiet one an instance on which it is false.

The requirement on the stub: ONE stub serves both halves. The same `fetch`,
layout and allocator must meet `Premises` (so the stub's code is
re-proved against `AllocatorContract`, both clauses, as `Stub.contract`
does for the quiet one), run the four calls of `Executed`, and at
`allocEntry` use its stack (a nonempty `A.depth`, a scratch byte changed)
and append to the coverage buffer (a byte of `c.writes` changed) from an
entry state with `c.Needed` and a success pending.

Acceptance: `theorem witnessHolds : WitnessHolds` in
`binary/C1Witness.lean`, namespace `Binary.Statements.C1.Proof`, standard
axioms only; `lake -d binary build` and `scripts/binary-proof-gate` pass.

## 3. Closing

When both theorems exist, phase 2 states `theorem signed : Signed :=
signed_of_referenced_and_witness referencedHolds witnessHolds`, registers
the headline in the gate and the surface, and writes the closing report.
None of that is done here.
