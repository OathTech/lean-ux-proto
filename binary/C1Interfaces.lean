import C1Step
import PairAllowedipsNodeBoundary
import CommonBitsCalls
import PairMappedMemory

/-! Result C1, proof plan: the interface propositions between the four work
packages, as `def … : Prop`. No theorem here. `C1Assembly` proves `Signed`
from them. Each proposition names the package that proves it and the landed
theorems it may use; `binary/Statements/C1/proof/PLAN.md` has the graph.

Reading guide. One accepted insertion is described once, on the source side,
by `StepFacts` (the mirror's run is the pure `C1Step.step`, with the walk
facts of `C1Invariant.walk`). Each path of the compiled code is then one
proposition `Path k`: from the invariant and the caller's conditions to the
conclusion of `InsertStep`, for runs whose step is case `k`. The packages
that execute instructions meet in three places only: the two service rules
(`AllocRule`, `FreeRule`, derived once from the signed contract) and one
machine cut inside `add` (`TrunkToNode`, the landed `NodeInit.boundary` at
`add+0x156` with what is needed to return from there). -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-! ## The node bound (derived from the signed text since revision 3) -/

/-- A node the service hands out ends strictly below 2^64. The landed
interpretation check (`Trie.validate`, inside `assertAt`, hence inside `Inv`)
demands `a + 72 < 2^64` of every node. Revision 2's `AllocResult` promised
only `a + 72 ≤ span.1 + span.2` with spans bounded by `≤ 2^64`, so this was a
hypothesis no package owned; revision 3 puts the bound into `AllocResult`'s
success clause and it is now `C1Assembly.nodeBelowTop`, one projection. The
paths that keep an allocated node still take it as a hypothesis, so their
statements are unchanged. `Statements/C1/proof/TopOfMemory.lean` keeps the
finding as a regression test. -/
def NodeBelowTop : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (live : List Nat) (record : HiddenRecord) (stream : List HiddenRecord) (t : MachineState),
    AllocResult L A live record stream t → record.bytes.head? = some 1 →
    t.data.regs.rax.toNat + nodeSize < 2^64

/-! ## The source side (package 1) -/

/-- The conclusion of `InsertStep` for one call. -/
def InsertPost (L : Layout) (A : Allocator) (c : Context) (s : MachineState) (w' : World)
    (ra : UInt64) (answer : Int) (t : MachineState) : Prop :=
  Returned s t ra ∧
  t.data.regs.get (.low .rax .W32) = BitVec.ofInt 32 answer ∧
  SeqAdvanced L s t ∧
  Inv L A w' t.data.dmem ∧
  EqualOutside (InsertWrites L A c s) s.data.dmem t.data.dmem

/-- The family's root slot and width, as the mirror's `insert` passes them. -/
def rootOf (d : Device) (family : Nat) : Option NodeId :=
  if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6
def widthOf (family : Nat) : Nat := if family == 4 then 32 else 128

/-- Everything the path packages are told about one accepted run of
`Leanux.WG.insert family key cidr pid` from `w` to `(answer, w')`: it is
`step` on the mirror's device `d` for the walk result `(placed, exact)` and
the outcomes of the pending records, up to `Allowedips.target`; it consumed
exactly the case's records, at the case's sites, each with outcome byte 0 or
1; the three sites stay armed; and, where the mirror reached the walk, the
walk's own accepted run (in the form the landed `Placement.loop_checked`
takes) and the ordering facts of `C1Invariant.walk`. -/
structure StepFacts (w : World) (family key cidr pid : Nat) (answer : Int) (w' : World)
    (d : Device) (stream : List HiddenRecord) (placed : Option NodeId) (exact : Bool)
    (st : Step) : Prop where
  device : w.wg.dev = some d
  records : w.ambient.hidden = some stream
  trie : ordered d = true
  families : family = 4 ∨ family = 6
  keyBound : key < 2^widthOf family
  model : st = Proof.step d family key cidr pid placed exact (stream.map fun r => r.bytes.head? == some 1)
  result : answer = st.answer
  after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target st.device
  recordsAfter : w'.ambient.hidden = some (stream.drop st.consumed)
  sites : (stream.take st.consumed).map (·.site) = st.case.sites
  outcomes : ∀ r ∈ stream.take st.consumed, r.bytes.head? = some 0 ∨ r.bytes.head? = some 1
  armedAfter : armed w' = true
  walked : st.case ≠ .tooLong → st.case ≠ .rootNoMem → st.case ≠ .root →
    (∃ ambient finalAmbient finalStore,
      ((WG.nodePlacement (rootOf d family) key cidr (widthOf family)).run (Source.Aip.store (bump d))).run ambient =
        .ok (((placed,exact),finalStore),finalAmbient)) ∧
    walk (bump d) (rootOf d family) key cidr (widthOf family) placed exact = true

/-- PACKAGE 1. Every accepted insertion under the invariant and the caller's
conditions is a `step`. May use: the mirror's definitions; `assertAt_ok`,
`heap_checks`, `Trie.heap` (for `ordered`); `AllowedipsSourceModel`,
`AllowedipsSourceRun`, `PairAllowedipsPlacementSource`,
`AllowedipsPlacementSourceStep`, `AllowedipsExactSource`,
`AllowedipsChildSource` (run equations already in the package); nothing from
`Leanux/Proofs`. Trial sources: T2 `CoverSource`, T4 `T4Source`, T5
`T5RootSource`, `T5Bridge`. -/
def RunIsStep : Prop :=
  ∀ (L : Layout) (A : Allocator) (c : Context) (s : MachineState) (w w' : World)
    (family key cidr pid : Nat) (ra : UInt64) (answer : Int),
    Inv L A w s.data.dmem →
    insertReady L A c s family key cidr pid ra = .ok () →
    (liftWG (WG.insert family key cidr pid)).run w = .ok (answer, w') →
    ∃ d stream placed exact st, StepFacts w family key cidr pid answer w' d stream placed exact st

/-- PACKAGE 1. `Initial` for `Inv`. May use: `assertAt_of_related`, the
decoders' definitions, `Premises` (nothing of it is needed). -/
def InitialHolds : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    Initial L A (Inv L A)

/-- PACKAGE 1. `Framed` for `Inv`. May use: `PairAllowedipsReadSet`,
`PairAllowedipsHeapFrame`, `PairAllowedipsFrame` (reconstruction and `heap`
depend only on the read spans), and the contract's `frame` clause for
`Idle`. -/
def FramedHolds : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    Framed L (Inv L A)

/-- PACKAGE 1 (new with revision 3 of the statement). `Referenced` for
`Inv`: a peer's count word moved by one together with the mirror's `peerGet`
or a non-releasing `peerPut`. `Inv` gives the count in memory equal to the
mirror's (`assertAt`'s reconstruction reads it), so the mirror's run changes
exactly that peer's `refcount` by one and nothing `Related` reads besides
(the pending records and the armed sites are untouched); the landed
`target_mapCounts`, `heap_mapCounts` (`PairAllowedipsCount`,
`PairAllowedipsHeapFrame`), which `lookup_checked` uses for the count
`wg_peer_get_maybe_zero` raises, carry the relation; the rest of the heap is
unchanged, so the reconstruction's other reads agree as in `FramedHolds`;
the count word is in a peer, apart from the arena (a conjunct of `Inv`), so
`Idle` survives by the contract's `frame` clause. -/
def ReferencedHolds : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    Referenced L (Inv L A)

/-- PACKAGE 1. `LookupStep` for `Inv`, from the landed `lookup_checked`
(`PairAllowedipsLookupAdequacy`): `lookupReady` and `Inv` give its
`lookupBoundary`; its post gives `Returned` and `rax`; `Trie.CountBytes` is
inside the heap; `Idle` survives by the contract's `frame` clause; the
mirror's lookup leaves the pending records and the armed sites alone. May
also use `const_cmp1_contract`-style transports for the one callback
contract `Premises` does not name directly (`CommonBits.Callbacks.constCmp1`). -/
def LookupHolds : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    LookupStep fetch L (Inv L A)

/-! ## The service rules (package 4, used by packages 2 and 3) -/

/-- A state `e` inside the insertion call that entered at `s`: its stack
pointer is within the insertion's window, memory differs from the entry's
only inside `InsertWrites`, every range readable at entry is still readable
(the landed `MappedLe`, the form `MemoryInvariant.eventually_mapped` gives),
the direction flag is clear and the coverage state is valid. -/
structure InFlight (L : Layout) (A : Allocator) (c : Context) (s e : MachineState) : Prop where
  low : s.data.regs.rsp.toNat ≤ e.data.regs.rsp.toNat + insertWindow
  high : e.data.regs.rsp.toNat ≤ s.data.regs.rsp.toNat
  frame : EqualOutside (InsertWrites L A c s) s.data.dmem e.data.dmem
  mapped : MappedLe s.data.dmem e.data.dmem
  forward : e.data.system.bits[10] = false
  coverage : c.At e.data.dmem

/-- The bytes a service called from `e` leaves alone: the live frames from
`e`'s return word up to and including the wrapper's return word, the table
and peer words, the nodes that stay handed out, and the `node_cache` word. -/
def Protected (L : Layout) (s e : MachineState) (kept : List Nat) (a : BitVec 64) : Prop :=
  InRange e.data.regs.rsp.toBitVec (s.data.regs.rsp.toNat + 8 - e.data.regs.rsp.toNat) a ∨
  (∃ span ∈ L.fixed, span.contains a) ∨ Kept kept a ∨ InRange (.ofNat 64 cacheWord) 8 a

/-- The table and the peers as whole objects (`Related`'s and `emptyTable`'s list). -/
def objectsOf (L : Layout) : List Pair.Span :=
  [(L.table,AllowedipsMutationLayout.tableSize)] ++ L.peers.map fun (_,a) => (a,Layouts.peerSize)

/-- The 72 bytes at `a` lie inside one arena span. -/
def InArena (L : Layout) (a : Nat) : Prop :=
  ∃ span ∈ L.arena, span.1 ≤ a ∧ a+nodeSize ≤ span.1+span.2

/-- PACKAGE 4. The allocation rule, derived once from
`AllocatorContract.alloc`: at the service's entry inside an insertion, with
the cache, the flags, a return site matching the pending record and the
allocator idle, the service returns with `AllocResult`, the call is still in
flight (stack, frame, mapping, direction flag, coverage), and every
protected byte is unchanged. The two static hypotheses (the table and peers
apart from the arena, the handed-out nodes inside it) are conjuncts of `Inv`
and of `AllocResult`; a caller has them. `ServiceReady` is established here from
`insertReady` and `InFlight`, its separation (`Separated`, revision 3 of the
statement) included: the caller's spans, the heap and the coverage spans are
pairwise apart by `frameReady`, and the service's stack lies in the caller's
stack span; the direction flag and the mapping across the
service body come from `SystemInvariant` and `MemoryInvariant`. May use
those, `PairStackBytes`, `spansApart_sound`, and the model of the landed
`PairInsertRandomReady` / `PairInsertRandomMemory` / `PairInsertRandomFrame`. -/
def AllocRule : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (c : Context) (s e : MachineState) (family key cidr pid : Nat) (ra back : UInt64)
    (live : List Nat) (record : HiddenRecord) (stream : List HiddenRecord),
    insertReady L A c s family key cidr pid ra = .ok () →
    spansApart (objectsOf L) L.arena = true → (∀ node ∈ live, InArena L node) →
    InFlight L A c s e →
    e.data.regs.rsp.toNat + 8 ≤ s.data.regs.rsp.toNat →
    e.pc = allocEntry → EntryFrame e back →
    e.data.regs.rdi.toNat = L.cache → e.data.regs.get (.low .rsi .W32) = 0xdc0#32 →
    (back.toNat, record.site) ∈ allocSites →
    A.Idle e.data.dmem live (record :: stream) →
    Eventually (instructionStep fetch) (fun t =>
      Returned e t back ∧ AllocResult L A live record stream t ∧ InFlight L A c s t ∧
      ∀ a, Protected L s e live a → t.data.dmem.get? a = e.data.dmem.get? a) e

/-- PACKAGE 4. The release rule, derived once from `AllocatorContract.free`. -/
def FreeRule : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (c : Context) (s e : MachineState) (family key cidr pid : Nat) (ra back : UInt64)
    (live : List Nat) (stream : List HiddenRecord),
    insertReady L A c s family key cidr pid ra = .ok () →
    spansApart (objectsOf L) L.arena = true → (∀ node ∈ live, InArena L node) →
    InFlight L A c s e →
    e.data.regs.rsp.toNat + 8 ≤ s.data.regs.rsp.toNat →
    e.pc = freeEntry → EntryFrame e back → back.toNat = freeSite →
    e.data.regs.rdi.toNat = L.cache → e.data.regs.rsi.toNat ∈ live →
    A.Idle e.data.dmem live stream →
    Eventually (instructionStep fetch) (fun t =>
      Returned e t back ∧ A.Idle t.data.dmem (live.erase e.data.regs.rsi.toNat) stream ∧
      InFlight L A c s t ∧
      ∀ a, Protected L s e (live.erase e.data.regs.rsi.toNat) a →
        t.data.dmem.get? a = e.data.dmem.get? a) e

/-! ## The paths (packages 2 and 3) -/

/-- One path of the compiled insertion, wrapper entry to the caller's return
address: `InsertStep` for the runs whose step is case `k`. -/
def Path (k : Case) : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (c : Context) (s : MachineState) (w w' : World) (family key cidr pid : Nat) (ra : UInt64)
    (answer : Int) (d : Device) (stream : List HiddenRecord) (placed : Option NodeId) (exact : Bool)
    (st : Step),
    Inv L A w s.data.dmem →
    insertReady L A c s family key cidr pid ra = .ok () →
    (liftWG (WG.insert family key cidr pid)).run w = .ok (answer, w') →
    StepFacts w family key cidr pid answer w' d stream placed exact st →
    st.case = k →
    Eventually (instructionStep fetch) (InsertPost L A c s w' ra answer) s

/-- The mirror's world at the cut: the wrapper has incremented the sequence. -/
def bumped (w : World) (d : Device) : World := {w with wg := {w.wg with dev := some (bump d)}}

/-- From the common exit of `add` (`add+0x549`, result in `ebx`) the machine
returns to the insertion's caller, whatever happened since `e` provided the
saved words above `add`'s locals are intact; on the way it writes only the
stack window and the coverage buffer, so the heap is unchanged and the
invariant is carried (by `Framed`). This is what package 2 hands package 3
in place of a description of the two frames. -/
def Exits (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) (c : Context)
    (s : MachineState) (ra : UInt64) (e : MachineState) : Prop :=
  ∀ x : MachineState, x.pc = AllowedipsMutationImage.Add.entry + 0x549 →
    x.data.regs.rsp = e.data.regs.rsp →
    InFlight L A c s x → CommonBitsCoverage.CallsReady c x.data →
    (∀ a, InRange (e.data.regs.rsp.toBitVec + 48) (s.data.regs.rsp.toNat + 8 - (e.data.regs.rsp.toNat + 48)) a →
      x.data.dmem.get? a = e.data.dmem.get? a) →
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      t.data.regs.get (.low .rax .W32) = x.data.regs.get (.low .rbx .W32) ∧
      EqualOutside (fun a => Scratch s (insertWindow + A.depth) a ∨ c.writes a) x.data.dmem t.data.dmem ∧
      (∀ a, L.Heap a → t.data.dmem.get? a = x.data.dmem.get? a) ∧
      (∀ w', Inv L A w' x.data.dmem → Inv L A w' t.data.dmem)) x

/-- The machine cut between packages 2 and 3: `add+0x156`, the first
allocation on a nonempty trie handed out and not yet initialized. The landed
executable `NodeInit.boundary` holds (the relation for the old
interpretation against the mirror's device with the sequence incremented,
the saved registers and locals, the zeroed object, the separations); the
interpretation is the layout's and inside the arena; `rbx` is the placed
node; the allocator is idle with the new object handed out and the first
record consumed; the call is in flight and the sequence word advanced; and
the common exit returns. -/
structure NodeCut (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) (c : Context)
    (s : MachineState) (ra : UInt64) (w : World) (d : Device) (key cidr pid : Nat)
    (stream : List HiddenRecord) (placed : Option NodeId)
    (names : Allowedips.Names) (base : Nat) (e : MachineState) : Prop where
  boundary : NodeInit.boundary names Root.nodeOffsets (bumped w d) e key cidr pid = .ok base
  table : names.table = L.table
  peers : names.trie.peers = L.peers
  arena : ∀ node ∈ names.trie.nodes, InArena L node.2
  fresh : InArena L base
  apart : spansApart (objectsOf L) L.arena = true
  idle : A.Idle e.data.dmem (names.trie.nodes.map (·.2) ++ [base]) (stream.drop 1)
  placedAt : Trie.address names.trie.nodes placed = .ok e.data.regs.rbx.toNat
  flight : InFlight L A c s e
  calls : CommonBitsCoverage.CallsReady c e.data
  seq : SeqAdvanced L s e
  exits : Exits fetch L A c s ra e

/-- PACKAGE 2, for package 3. Wrapper entry to `add+0x156` for the cases
that go on below the placement with a node there. May use: `increment_region`,
`Placement.loop_checked`, `common_checked`, the landed callback contracts,
`AllocRule`, `Return.{add_checked,wrapper_checked,finish_checked}` (for
`Exits`). Trial source: T4 (`T4Prologue`, `T4Entry`, `T4Stack`, `T4Reach`,
`T4Return`; its contract and entry assertion are superseded). -/
def TrunkToNode : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (c : Context) (s : MachineState) (w w' : World) (family key cidr pid : Nat) (ra : UInt64)
    (answer : Int) (d : Device) (stream : List HiddenRecord) (placed : Option NodeId) (exact : Bool)
    (st : Step),
    Inv L A w s.data.dmem →
    insertReady L A c s family key cidr pid ra = .ok () →
    StepFacts w family key cidr pid answer w' d stream placed exact st →
    st.case = .cover ∨ st.case = .split ∨ st.case = .splitNoMem →
    Eventually (instructionStep fetch) (fun e => ∃ names base,
      NodeCut fetch L A c s ra w d key cidr pid stream placed names base e) s

/-! Package 2's propositions take `FramedHolds` (package 1) as a hypothesis:
every path ends by carrying `Inv` across the epilogues' stack and coverage
writes, which is `Framed`. Package 3 gets that through `Exits`. -/

/-- PACKAGE 2. Over-long prefix: `-EINVAL` (both wrappers). No service call. -/
def PathTooLong : Prop := FramedHolds → Path .tooLong
/-- PACKAGE 2. Empty root, the allocation at :190 refused. -/
def PathRootNoMem : Prop := FramedHolds → AllocRule → Path .rootNoMem
/-- PACKAGE 2. Empty root. May use `Root.initialization_checked`. -/
def PathRoot : Prop := NodeBelowTop → FramedHolds → AllocRule → Path .root
/-- PACKAGE 2. Exact match. May use `Exact.assignment_from_relation`. -/
def PathExact : Prop := FramedHolds → Path .exact
/-- PACKAGE 2. The allocation at :205 refused. -/
def PathNodeNoMem : Prop := FramedHolds → AllocRule → Path .nodeNoMem
/-- PACKAGE 2. Child attachment. May use `ChildFinish.initialization_child_checked`. -/
def PathChild : Prop := NodeBelowTop → FramedHolds → AllocRule → Path .child
/-- PACKAGE 2. The trunk to the cut, for package 3. -/
def TrunkHolds : Prop := NodeBelowTop → FramedHolds → AllocRule → TrunkToNode
/-- PACKAGE 3. Covering node, at the root and below a parent. May use
`NodeInit.initialization_core_checked`, `common_checked`, and T1, T2 as
lemma sources. -/
def PathCover : Prop := TrunkToNode → Path .cover
/-- PACKAGE 3. Intermediate node, two allocations, at the root and below a
parent. T5 as lemma source. -/
def PathSplit : Prop := NodeBelowTop → AllocRule → TrunkToNode → Path .split
/-- PACKAGE 3. The second allocation refused: unlink, release, `-ENOMEM`. -/
def PathSplitNoMem : Prop := AllocRule → FreeRule → TrunkToNode → Path .splitNoMem

/-! ## The headline with the invariant fixed, and what follows from it -/

/-- The four clauses of `Headline` for `Inv` that revision 2 had; the fifth,
`Referenced`, is `ReferencedHolds`, kept apart so that the exclusions, which
do not need it, keep their statements. -/
def HeadlineFor : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
    Initial L A (Inv L A) ∧ Framed L (Inv L A) ∧
    InsertStep fetch L A (Inv L A) ∧ LookupStep fetch L (Inv L A)

/-- PACKAGE 1. Exclusion 1 from the headline: the mirror facts needed are
that the first step at an empty table with outcome 1 is case `root` with
answer 0, and that the lookup the hypothesis accepts then finds `pid`. -/
def ExclusionOne : Prop := HeadlineFor → InsertThenLookup
/-- PACKAGE 1. Exclusion 2 from the headline: case `rootNoMem`, answer
`-ENOMEM`, the device unchanged up to the sequence, the lookup finds nothing. -/
def ExclusionTwo : Prop := HeadlineFor → FailedInsertInvisible

/-! ## The witness (package 4) -/

/-- PACKAGE 4. `__sanitizer_cov_trace_cmp1` from the image's terms, in the
manner of the landed `Callback.cmp4_contract`. This and the next two are the
only places the plan mentions `CallbacksFromImage`. -/
def Cmp1FromImage : Prop :=
  ∀ fetch : Int64 → Option Decoded, CallbacksFromImage fetch → AllowedipsTraceCmp1Contract fetch
/-- PACKAGE 4. `__sanitizer_cov_trace_cmp8` from the image's terms. -/
def Cmp8FromImage : Prop :=
  ∀ fetch : Int64 → Option Decoded, CallbacksFromImage fetch → AllowedipsTraceCmp8Contract fetch
/-- PACKAGE 4. Some `fetch`, layout and allocator meet every premise with
the callbacks the image's and a stub, in instruction terms, at the two
service addresses, with a nonempty scratch. -/
def PremisesMet : Prop :=
  ∃ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator),
    Premises fetch L A ∧ CallbacksFromImage fetch ∧ 0 < A.depth
/-- PACKAGE 4. The witness. It may use the headline (to run the four calls
through `InsertStep` and `LookupStep` at its own `fetch`) or execute them
directly, as the landed `PairInsertWitness` does. -/
def WitnessHolds : Prop := HeadlineFor → Witness

end Binary.Statements.C1.Proof
