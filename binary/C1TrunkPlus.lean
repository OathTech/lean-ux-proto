import C1TrunkCut
/-! Result C1, package 2: the trunk in its strengthened form. `to_trunk`
reaches `add`'s entry with `Trunk` for an arbitrary continuation (the first
half of `through_core`, copied); `trunk_to_cut` joins the walk, the
allocation and the cut; `trunkToNodePlus` is the trunk package 3 uses
(`TrunkToNodePlus`, copied from `task/binary-c1-wp3` at 3738c868,
`binary/C1BelowTrunk.lean`, because importing that module would bring
package 3's proofs with it), under `StackOffPeers` (see `C1TrunkCut`). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- The wrapper's entry to `add`'s entry, for any continuation. -/
theorem to_trunk (fetch : Int64 → Option Decoded) (L : Statements.C1.Layout) (A : Allocator)
    (premises : Premises fetch L A) (c : Context) (s : MachineState) (w : World)
    (v4 : Bool) (key cidr pid : Nat) (ra : UInt64)
    (inv : Inv L A w s.data.dmem)
    (pc : s.pc = if v4 then Insert4.entry else Insert6.entry)
    (tableReg : s.data.regs.rdi.toNat = L.table)
    (peer : Trie.address L.peers (some pid) = .ok s.data.regs.rcx.toNat)
    (peerNonNull : s.data.regs.rcx.toNat ≠ 0)
    (cidrReg : s.data.regs.rdx.toNat % 256 = cidr)
    (keyAt : Binary.Allowedips.NetworkKey s.data.dmem s.data.regs.rsi.toBitVec (if v4 then 32 else 128) key)
    (cache : readNat s cacheWord 8 = .ok L.cache)
    (frame : FrameFacts L c s ra (insertWindow + A.depth) (s.data.regs.rsi.toNat, if v4 then 4 else 16))
    (P : MachineState → Prop)
    (body : ∀ names stream d seq a, Trunk L A c s w v4 key cidr pid ra names stream d seq a →
      Eventually (instructionStep fetch) P ⟨a,Add.entry⟩) :
    Eventually (instructionStep fetch) P s := by
  have wide := window_wide A
  have sep := frame.separate
  obtain ⟨names,stream,tableEq,peersEq,asserted,armedW,hiddenW,sitesW,objectsApart,inArena,idle⟩ := inv
  obtain ⟨d,device,related,shape⟩ := assertAt_ok asserted
  obtain ⟨seq,seqWord⟩ := seq_exists related
  have address := seq_address s.data.regs.rdi names.table (tableReg.trans tableEq.symm)
  rw [← address] at seqWord
  have wideStack (x : BitVec 64) (h : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 200) 208 x) :
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth + 8) x :=
    below_sub _ 200 208 (insertWindow + A.depth) (insertWindow + A.depth + 8) wide (by have := wide; omega) x h
  have caller : Caller c s.data seq := {
    aligned := frame.entry.1
    room := by have := sep.room; omega
    below := fun i hi => frame.mapped i (by omega)
    coverage := frame.coverage
    coverageStack := fun x read h => sep.bytesStack x read (wideStack x h)
    metadataSeparate := sep.writesMetadata
    preemptSeparate := sep.writesPreempt
    seqWord := seqWord
    seqStack := fun x h hs => sep.heapStack x (seq_heap _ tableReg x h) (wideStack x hs)
    seqCoverage := fun x h => sep.heapBytes x (seq_heap _ tableReg x h) }
  have entered := enter fetch premises.insertion premises.tracePc caller v4 key keyAt
    (fun x h hs => sep.stackQuery x (below_sub _ 200 200 _ _ wide (by omega) x hs) h)
    (fun x h hw => sep.writesQuery x hw h)
    (fun x h hq => sep.heapQuery x (seq_heap _ tableReg x hq) h)
  have run := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch entered)
  have start : s = ⟨s.data,if v4 then Insert4.entry else Insert6.entry⟩ := Placement.at_pc s _ pc
  rw [start]
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro a ⟨⟨⟨pcA,atAdd⟩,mapped⟩,_,forwardA⟩
  obtain ⟨relatedA,shapeA⟩ := related_at_add wide sep tableEq peersEq inArena tableReg seqWord related shape atAdd
  have trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a.data := {
    tableReg, peer, peerNonNull, cidr := cidrReg, cache, entry := frame.entry, capacity := frame.capacity
    forward := frame.forward, stackMapped := frame.mapped, sep, table := tableEq, peers := peersEq
    related, shape, device, armed := armedW, hidden := hiddenW, sites := sitesW, objectsApart, inArena
    idle, caller, atAdd, mapped
    forwardA := forwardA.trans frame.forward
    relatedA, shapeA }
  rw [Placement.at_pc a _ pcA]
  exact body names stream d seq a.data trunk

/-- Copied verbatim from package 3 (see the module comment), with this
package's copy of `CutExtra`. -/
def TrunkToNodePlus : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Statements.C1.Layout) (A : Allocator), Premises fetch L A →
  ∀ (c : Context) (s : MachineState) (w w' : World) (family key cidr pid : Nat) (ra : UInt64)
    (answer : Int) (d : Device) (stream : List HiddenRecord) (placed : Option NodeId) (exact : Bool)
    (st : Proof.Step),
    Inv L A w s.data.dmem →
    insertReady L A c s family key cidr pid ra = .ok () →
    StepFacts w family key cidr pid answer w' d stream placed exact st →
    st.case = .cover ∨ st.case = .split ∨ st.case = .splitNoMem →
    Eventually (instructionStep fetch) (fun e => ∃ names base,
      NodeCut fetch L A c s ra w d key cidr pid stream placed names base e ∧
      CutExtra L s e family) s

/-- The strengthened trunk gives the interface's trunk (after package 3's `trunk_of_plus`). -/
theorem trunk_of_plus (trunk : TrunkToNodePlus) : TrunkToNode := by
  intro fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st inv ready facts case
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (trunk fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st inv ready facts case)
  rintro e ⟨names,base,cut,_⟩
  exact ⟨names,base,cut⟩

/-- The first pending record of a case that allocates at :205. -/
theorem first_site {stream : List HiddenRecord} {n : Nat} {tail : List Nat}
    (sites : (stream.take n).map (·.site) = 78 :: tail) :
    ∃ record rest, stream = record :: rest ∧ record.site = 78 := by
  cases stream with
  | nil => simp at sites
  | cons record rest =>
    cases n with
    | zero => simp at sites
    | succ k =>
      simp at sites
      exact ⟨record,rest,rfl,sites.1⟩

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- Nonempty root, no exact match, the service hands out an object: `add`'s
entry to +0x156 with the allocation's result. -/
theorem node_allocated (below : NodeBelowTop) (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128)) (keyBound : key < 2^(if v4 then 32 else 128))
    (rootId : NodeId)
    (rootAt : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId)
    (rootNode : ∃ node, (bump d).nodes.get? rootId = some node ∧ node.bitlen = (if v4 then 32 else 128))
    (placed : Option NodeId)
    (ambient finalAmbient : Ambient) (finalStore : AipStore)
    (accepted : ((WG.nodePlacement (some rootId) key cidr (if v4 then 32 else 128)).run
      (Source.Aip.store (bump d))).run ambient = .ok (((placed,false),finalStore),finalAmbient))
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 78) (ok : record.bytes.head? = some 1) :
    Eventually (instructionStep fetch) (fun v => ∃ word : UInt64,
      v.pc = Add.entry+0x156 ∧
      Mid L A c s v4 names d seq a (if v4 then 32 else 128) placed word v.data ∧
      Object L names word.toNat ∧ readNat v word.toNat 72 = .ok 0 ∧
      A.Idle v.data.dmem (names.trie.nodes.map (·.2) ++ [word.toNat]) rest) ⟨a,Add.entry⟩ := by
  apply eventually_trans (instructionStep fetch) _ _ _
    (trunk_walked premises trunk bound keyBound rootId rootAt rootNode placed false
      ambient finalAmbient finalStore accepted)
  intro t walked
  obtain ⟨bpT,r14T⟩ := walked.open' rfl
  apply eventually_trans (instructionStep fetch) _ _ _ (node_reach premises trunk walked)
  rintro e ⟨u,at',bx,bp,r14,r15⟩
  apply eventually_trans (instructionStep fetch) _ _ _
    (node_called (bits := if v4 then 32 else 128) alloc premises ready trunk at' (bx.trans walked.rbx) (by rw [bp]; exact bpT)
      (r14.trans r14T) (by rw [r15]; exact walked.r15) record rest pending recordSite)
  rintro b ⟨t1,result,mid,pcB,_,heapB⟩
  obtain ⟨object,zero1,idle1⟩ := object_of_result below premises trunk result ok
  have nonNull : t1.data.regs.rax.toBitVec ≠ 0 := by
    intro h
    have zero : t1.data.regs.rax.toNat = 0 := by
      show t1.data.regs.rax.toBitVec.toNat = 0
      rw [h]
      rfl
    have positive := object.positive
    omega
  rw [ite_eq_right nonNull] at pcB
  rw [Placement.at_pc b _ pcB]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (mid.call premises trunk (Add.entry+0x151) (premises.insertion.add _ _ (by rfl)))
  rintro v ⟨pcV,midV,heapV⟩
  have heapSame : ∀ y, L.Heap y → v.data.dmem.get? y = t1.data.dmem.get? y :=
    fun y hy => (heapV y hy).trans (heapB y hy)
  have nodeHeap (y : BitVec 64) (inside : InRange (.ofNat 64 t1.data.regs.rax.toNat) 72 y) : L.Heap y := by
    obtain ⟨home,isArena,low,high⟩ := object.arena
    exact arena_heap y ⟨home,isArena,span_within _ _ _ _ low (by unfold nodeSize at high; omega) y inside⟩
  refine ⟨t1.data.regs.rax,pcV,midV,object,?_,?_⟩
  · rw [← readNat_frame (before := t1) (after := v) (writes := fun y => ¬L.Heap y)
      (fun y hy => (heapSame y (Classical.not_not.mp hy)).symm) _ 72
      (fun y inside => not_not_intro (nodeHeap y inside))]
    exact zero1
  · exact premises.allocator.frame t1.data.dmem v.data.dmem _ _ idle1
      (fun y arena _ => (heapSame y (arena_heap y arena)).symm)

/-- Nonempty root, no exact match, the object handed out: `add`'s entry to the cut. -/
theorem trunk_to_cut (below : NodeBelowTop) (framed : FramedHolds) (alloc : AllocRule)
    (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (peersOff : ∀ peer ∈ L.peers, ∀ x,
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x →
      ¬Pair.Span.contains (peer.2,Layouts.peerSize) x)
    (bound : cidr ≤ (if v4 then 32 else 128)) (keyBound : key < 2^(if v4 then 32 else 128))
    (rootId : NodeId)
    (rootAt : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId)
    (rootNode : ∃ node, (bump d).nodes.get? rootId = some node ∧ node.bitlen = (if v4 then 32 else 128))
    (placed : Option NodeId)
    (present : ∀ id, placed = some id → ∃ n, (bump d).nodes.get? id = some n)
    (ambient finalAmbient : Ambient) (finalStore : AipStore)
    (accepted : ((WG.nodePlacement (some rootId) key cidr (if v4 then 32 else 128)).run
      (Source.Aip.store (bump d))).run ambient = .ok (((placed,false),finalStore),finalAmbient))
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 78) (ok : record.bytes.head? = some 1)
    (families : family = if v4 then 4 else 6) :
    Eventually (instructionStep fetch) (fun e => ∃ names' base,
      NodeCut fetch L A c s ra w d key cidr pid stream placed names' base e ∧
      CutExtra L s e family) ⟨a,Add.entry⟩ := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (node_allocated below alloc premises ready trunk bound keyBound rootId rootAt rootNode placed
      ambient finalAmbient finalStore accepted record rest pending recordSite ok)
  rintro v ⟨word,pcV,mid,object,zero,idle⟩
  exact ⟨names,word.toNat,node_cut framed premises trunk peersOff bound present family families pcV mid
    object zero (by subst pending; exact idle)⟩
end

/-- PACKAGE 2, for package 3: the trunk in the strengthened form, from the
three hypotheses of `TrunkHolds` and `StackOffPeers`. -/
theorem trunkToNodePlus (off : StackOffPeers) (below : NodeBelowTop) (framed : FramedHolds)
    (alloc : AllocRule) : TrunkToNodePlus := by
  intro fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st inv ready
    facts hcase
  have rf := insertReady_facts ready
  have hcase' := hcase
  rw [facts.model] at hcase'
  obtain ⟨notExact,okHead⟩ := step_below hcase'
  obtain ⟨bound,rootId,rootAt⟩ := step_walked_of (.inr (.inr (.inr hcase')))
  subst notExact
  obtain ⟨⟨ambient,finalAmbient,finalStore,accepted⟩,walkFact⟩ := facts.walked
    (fun h => by rcases hcase with k | k | k <;> rw [k] at h <;> cases h)
    (fun h => by rcases hcase with k | k | k <;> rw [k] at h <;> cases h)
    (fun h => by rcases hcase with k | k | k <;> rw [k] at h <;> cases h)
  obtain ⟨record,rest,pending,recordSite⟩ : ∃ record rest, stream = record :: rest ∧ record.site = 78 := by
    have sites := facts.sites
    rcases hcase with k | k | k <;> rw [k] at sites <;> exact first_site sites
  have ok : record.bytes.head? = some 1 := by
    subst pending
    simpa using okHead
  have present : ∀ id, placed = some id → ∃ n, (bump d).nodes.get? id = some n := by
    intro id h
    subst h
    obtain ⟨p,hp,_⟩ := walk_placed walkFact
    exact ⟨p,hp⟩
  have rootNode := ordered_root facts.trie rootAt
  have peersOff := off L A c s family key cidr pid ra ready
  rcases rf.families with rfl | rfl
  · exact to_trunk fetch L A premises c s w true key cidr pid ra inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = stream := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact trunk_to_cut below framed alloc premises ready trunk peersOff bound facts.keyBound rootId
          rootAt rootNode placed present ambient finalAmbient finalStore
          (by rw [show rootOf d0 4 = some rootId from rootAt] at accepted; exact accepted)
          record rest pending recordSite ok rfl)
  · exact to_trunk fetch L A premises c s w false key cidr pid ra inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = stream := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact trunk_to_cut below framed alloc premises ready trunk peersOff bound facts.keyBound rootId
          rootAt rootNode placed present ambient finalAmbient finalStore
          (by rw [show rootOf d0 6 = some rootId from rootAt] at accepted; exact accepted)
          record rest pending recordSite ok rfl)

#print axioms to_trunk
#print axioms node_allocated
#print axioms trunk_to_cut
#print axioms trunkToNodePlus
end C1Trunk
