import C1TrunkNodeNoMem
import C1TrunkSourceChild
import AllowedipsChildChecked
import AllowedipsAllocationNames
/-! Result C1, package 2: child attachment. From `add`'s entry through the
walk and the allocation to the cut at +0x156, then the landed
`ChildFinish.initialization_child` (its caller resources derived here from
`Trunk` and the state after the service, not from the executable
`ChildResources.resources`), and the common finish. The landed theorem takes
`NodeInit.boundary`, so this path inherits `StackOffPeers` (see
`C1TrunkCut`). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
open Binary.Pair.Allowedips.ChildFinish
local instance : Labels := Image.linkedLabels

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w w' : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- The table's 24 bytes are heap words. -/
theorem Trunk.tableHeap (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (x : BitVec 64) (inside : InRange (.ofNat 64 names.table) 24 x) : L.Heap x := by
  obtain ⟨i,hi,eq⟩ := inside
  have tableEq : names.table = L.table := trunk.table
  have shift (b : Nat) (hb : b ≤ i) : x = BitVec.ofNat 64 (L.table+b) + .ofNat 64 (i-b) := by
    rw [eq, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    show names.table + i = L.table + b + (i - b)
    omega
  by_cases first : i < 8
  · exact ⟨(L.table+0,8),by simp [Layout.heap, Layout.fixed, tableFields,
      AllowedipsMutationLayout.root4],⟨i-0,by omega,shift 0 (by omega)⟩⟩
  · by_cases second : i < 16
    · exact ⟨(L.table+8,8),by simp [Layout.heap, Layout.fixed, tableFields,
        AllowedipsMutationLayout.root6],⟨i-8,by omega,shift 8 (by omega)⟩⟩
    · exact ⟨(L.table+16,8),by simp [Layout.heap, Layout.fixed, tableFields,
        AllowedipsMutationLayout.seq],⟨i-16,by omega,shift 16 (by omega)⟩⟩

/-- Child attachment: `add` from its entry to the insertion's return. -/
theorem child_body (below : NodeBelowTop) (framed : FramedHolds) (alloc : AllocRule)
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
    (p : NodeId) (parentNode : AipNode) (hasParent : (bump d).nodes.get? p = some parentNode)
    (sameWidth : parentNode.bitlen = (if v4 then 32 else 128)) (measure : parentNode.cidr < cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr) =
      parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (empty : parentNode.bit[key/2^(parentNode.bitlen-1-parentNode.cidr)%2]? = some none)
    (ambient finalAmbient : Ambient) (finalStore : AipStore)
    (accepted : ((WG.nodePlacement (some rootId) key cidr (if v4 then 32 else 128)).run
      (Source.Aip.store (bump d))).run ambient = .ok (((some p,false),finalStore),finalAmbient))
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 78) (ok : record.bytes.head? = some 1)
    (after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target
      (chooseConnect (addTail (Proof.alloc (bump d) (newNode key cidr (if v4 then 32 else 128) (some pid)))
        pid (bump d).nextNode) p (bump d).nextNode))
    (recordsAfter : w'.ambient.hidden = some rest) (armedAfter : armed w' = true) :
    Eventually (instructionStep fetch) (InsertPost L A c s w' ra 0) ⟨a,Add.entry⟩ := by
  apply eventually_trans (instructionStep fetch) _ _ _
    (node_allocated below alloc premises ready trunk bound keyBound rootId rootAt rootNode (some p)
      ambient finalAmbient finalStore accepted record rest pending recordSite ok)
  rintro v ⟨word,pcV,mid,object,zero,idle⟩
  have fs := frameSize_range v4
  have wide := window_wide A
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have top' : s.data.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 := trunk.sep.top
  have stackAt := trunk.atAdd.stackAt
  have vspBV := mid.stackAt trunk
  have vspNat : v.data.regs.rsp.toNat = s.data.regs.rsp.toBitVec.toNat - (frameSize v4 + 96) := by
    show v.data.regs.rsp.toBitVec.toNat = _
    rw [vspBV, toNat_sub_ofNat _ _ (by omega)]
  have direction : key/2^(parentNode.bitlen-1-parentNode.cidr)%2 < 2 := Nat.mod_lt _ (by decide)
  have checked := node_boundary (w := w) trunk peersOff bound pcV mid object zero
  have present : ∀ id, some p = some id → ∃ n, (bump d).nodes.get? id = some n :=
    fun id h => by cases h; exact ⟨parentNode,hasParent⟩
  have parentNamed : (p,v.data.regs.rbx.toNat) ∈ names.trie.nodes :=
    (placed_address mid.related present mid.rbx).2 p rfl
  have ownerAt : Trie.address names.trie.peers (some pid) = .ok v.data.regs.r14.toNat := by
    rw [mid.r14, trunk.atAdd.peer, trunk.peers]
    exact trunk.peer
  obtain ⟨owner,_,hasPeer⟩ := Root.peer_of_address ownerAt mid.related
  have different : (bump d).nextNode ≠ p := by
    have belowCounter := ids_below_counter (related_valid trunk.relatedA) _ parentNamed
    have counter : (bump d).nextNode = names.nextNode := (Allowedips.reconstruct_fields trunk.relatedA).nextNode
    change p < names.nextNode at belowCounter
    intro h
    rw [counter] at h
    rw [h] at belowCounter
    exact Nat.lt_irrefl _ belowCounter
  -- the three kinds of written bytes
  let fake : MachineData := {v.data with regs := {v.data.regs with rbx := word}}
  have spans := object.writeSpans trunk fake rfl
  have heapFacts (y : BitVec 64)
      (h : InRange (.ofNat 64 word.toNat) 72 y ∨ ListWrites (names.allocated word.toNat) y) :
      L.Heap y ∧ ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 y ∧
        (L.Arena y → Kept (names.trie.nodes.map (·.2) ++ [word.toNat]) y) := by
    obtain ⟨span,member,inside⟩ := Root.writeSpans_cover (names.allocated word.toNat) fake y
      (h.elim .inl (fun l => .inr (.inl l)))
    exact ⟨(spans span member).2.1 y inside,(spans span member).2.2.1 y inside,
      (spans span member).2.2.2 y inside⟩
  have parentFacts (y : BitVec 64) (h : InRange (.ofNat 64 (v.data.regs.rbx.toNat+
        key/2^(parentNode.bitlen-1-parentNode.cidr)%2*8+8)) 8 y) :
      L.Heap y ∧ ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 y ∧
        (L.Arena y → Kept (names.trie.nodes.map (·.2) ++ [word.toNat]) y) := by
    obtain ⟨home,isArena,low,high⟩ := trunk.inArena _ parentNamed
    unfold nodeSize at high
    have inArena : L.Arena y := ⟨home,isArena,span_within _ _ _ _ (by show home.1 ≤ _; omega)
      (by show _ ≤ home.1 + home.2; omega) y h⟩
    refine ⟨arena_heap y inArena,arena_not_seq trunk.objectsApart y inArena,fun _ => ?_⟩
    exact ⟨v.data.regs.rbx.toNat,List.mem_append_left _ (List.mem_map.mpr ⟨_,parentNamed,rfl⟩),
      span_within _ _ _ _ (by omega) (by unfold nodeSize; omega) y h⟩
  have stackIn (k len : Nat) (hk : k + len ≤ 48) (y : BitVec 64)
      (h : InRange (.ofNat 64 (v.data.regs.rsp.toNat+k)) len y) :
      InRange (a.regs.rsp.toBitVec-104) 56 y := by
    rw [mid.stack, frame_address] at h
    obtain ⟨i,hi,eq⟩ := h
    exact ⟨8+k+i,by omega,by rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  have lowWide (y : BitVec 64) (h : InRange (a.regs.rsp.toBitVec-104) 56 y) : Wide a y :=
    wide_sub a 0 56 (by decide) y (by simpa using h)
  have spZero : v.data.regs.rsp.toBitVec = a.regs.rsp.toBitVec-104+.ofNat 64 8 := by
    have h := sp_frame a v.data.regs.rsp mid.stack 0
    simpa using h
  have setupStack (y : BitVec 64) (h : ChildSetup.Writes v.data.regs.rsp y) :
      InRange (a.regs.rsp.toBitVec-104) 56 y := by
    have h' : InRange v.data.regs.rsp.toBitVec 32 y := h
    rw [spZero] at h'
    obtain ⟨i,hi,eq⟩ := h'
    exact ⟨8+i,by omega,by rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]⟩
  have callWord (y : BitVec 64) (h : InRange (v.data.regs.rsp.toBitVec-8) 8 y) :
      InRange (a.regs.rsp.toBitVec-104) 56 y := by
    rw [call_word a v.data mid.stack] at h
    exact range_mono _ 8 56 (by omega) y h
  have entryClass (y : BitVec 64) (h : NodeInit.EntryWrites names v.data word.toNat y) :
      (L.Heap y ∧ ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 y ∧
        (L.Arena y → Kept (names.trie.nodes.map (·.2) ++ [word.toNat]) y)) ∨
      InRange (a.regs.rsp.toBitVec-104) 56 y := by
    rcases h with b | l | ⟨offset,member,inside⟩
    · exact .inl (heapFacts y (.inl b))
    · exact .inl (heapFacts y (.inr l))
    · have small : offset + 1 ≤ 48 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        omega
      exact .inr (stackIn offset 1 small y inside)
  have publishClass (y : BitVec 64) (h : PublishWrites v.data.regs.rbx word.toNat
        (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) y) :
      L.Heap y ∧ ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 y ∧
        (L.Arena y → Kept (names.trie.nodes.map (·.2) ++ [word.toNat]) y) := by
    rcases h with b | q
    · exact heapFacts y (.inl (span_within _ _ _ _ (by omega) (by omega) y b))
    · exact parentFacts y q
  have setupWide (y : BitVec 64) (h : SetupWrites v.data.regs.rsp c y) : Wide a y ∨ c.writes y := by
    rcases h with su | call | cw
    · exact .inl (lowWide y (setupStack y su))
    · exact .inl (lowWide y (callWord y call))
    · exact .inr cw
  have heapNotSetup (y : BitVec 64) (heap : L.Heap y) : ¬SetupWrites v.data.regs.rsp c y :=
    fun h => (setupWide y h).elim (trunk.heapWide y heap).1 (trunk.heapWide y heap).2
  have r13BV : v.data.regs.r13.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (if v4 then 36 else 48) := by
    rw [mid.r13, trunk.atAdd.query]
    cases v4 <;> rfl
  have nq : (if v4 then 32 else 128)/8 ≤ (if v4 then 36 else 48) + 8 ∧
      (if v4 then 36 else 48) + 8 ≤ frameSize v4 := by cases v4 <;> decide
  have run := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch
    (initialization_child fetch premises.insertion premises.tracePc c checked rfl parentNamed hasParent
      hasPeer (mid.rbp.trans sameWidth.symm) measure prefixEq empty
      (by rw [vspNat]; omega)
      (fun offset size fits => by
        rw [BitVec.ofNat_add, Root.ofNat_uint64, vspBV, sub_add_ofNat _ _ offset (by omega)]
        exact mid.mapped _ _ (trunk.caller.below.load _ size (by omega) (by omega)))
      mid.ready
      (fun y read h => (entryClass y h).elim (fun heap => trunk.sep.heapBytes y heap.1 read)
        (fun low => trunk.bytesWide y read (lowWide y low)))
      (fun y read h => trunk.bytesWide y read (lowWide y (setupStack y h)))
      (fun y read h => trunk.sep.heapBytes y (publishClass y h).1 read)
      (fun y h hc => by
        rcases hc with call | cw
        · have h' : InRange v.data.regs.rsp.toBitVec 32 y := h
          rw [spZero] at h'
          rw [call_word a v.data mid.stack] at call
          exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) 8 32 0 8 (by omega) (by omega)
            (.inr (by omega)) y h' (by simpa using call)
        · exact trunk.bytesWide y (writes_bytes cw) (lowWide y (setupStack y h)))
      (fun span member y inside => heapNotSetup y
        (read_heap (names := names.allocated word.toNat) trunk.table trunk.peers (object.inArena trunk)
          span member y inside))
      (fun y inside => heapNotSetup y (trunk.tableHeap y inside))
      (fun y inside h => by
        rw [r13BV, sameWidth] at inside
        rcases setupWide y h with hw | cw
        · exact below_under _ _ _ (insertWindow + A.depth) _ (by omega) (by omega) (by omega) y inside
            (wide_tight trunk.atAdd (insertWindow + A.depth) wide y hw)
        · exact trunk.sep.bytesStack y (writes_bytes cw)
            (below_sub _ _ _ (insertWindow + A.depth) (insertWindow + A.depth + 8) (by omega) (by omega)
              y inside))
      (fun y h hc => by
        have heap := (publishClass y h).1
        rcases hc with call | cw
        · exact (trunk.heapWide y heap).1 (lowWide y (callWord y call))
        · exact (trunk.heapWide y heap).2 cw)
      (fun y hs hb => (trunk.heapWide y
        (heapFacts y (.inl (span_within _ _ _ _ (by omega) (by omega) y hb))).1).1
        (lowWide y (stackIn 16 8 (by omega) y hs)))))
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro x ⟨⟨⟨pcX,rbxX,spX,readyX,frameX,relatedX,shapeX⟩,mappedX⟩,_,forwardX⟩
  have classify (y : BitVec 64)
      (h : NodeInit.EntryWrites names v.data word.toNat y ∨ SetupWrites v.data.regs.rsp c y ∨
        PublishWrites v.data.regs.rbx word.toNat (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) y) :
      (L.Heap y ∧ ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 y ∧
        (L.Arena y → Kept (names.trie.nodes.map (·.2) ++ [word.toNat]) y)) ∨
      InRange (a.regs.rsp.toBitVec-104) 56 y ∨ c.writes y := by
    rcases h with e | (su | call | cw) | pb
    · exact (entryClass y e).elim .inl (fun low => .inr (.inl low))
    · exact .inr (.inl (setupStack y su))
    · exact .inr (.inl (callWord y call))
    · exact .inr (.inr cw)
    · exact .inl (publishClass y pb)
  have flightV := mid.flight trunk v.pc
  have flightX : InFlight L A c s x := by
    refine ⟨by rw [spX]; exact flightV.low,by rw [spX]; exact flightV.high,?_,
      fun y k h => mappedX y k (mid.mapped y k h),forwardX.trans mid.forward,readyX.state⟩
    intro y hy
    refine (flightV.frame y hy).trans (frameX y (fun h => hy ?_))
    rcases classify y h with heap | low | cw
    · exact .inr (.inr heap.1)
    · exact .inl (range_mono _ _ _ (by omega) y (wide_tight trunk.atAdd _ wide y (lowWide y low)))
    · exact .inr (.inl cw)
  have lowBase : a.regs.rsp.toBitVec - 104 =
      s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104) := by
    show a.regs.rsp.toBitVec - BitVec.ofNat 64 104 = _
    rw [stackAt, sub_sub_ofNat]
  refine finish_exit (mid.exits framed premises trunk v.pc) pcX spX flightX readyX ?_
    (ebx_zero _ rbxX) ?_ ?_
  · intro y hy
    have base : v.data.regs.rsp.toBitVec + 48 =
        s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48) := by
      rw [vspBV]
      show _ + BitVec.ofNat 64 48 = _
      rw [sub_add_ofNat _ _ 48 (by omega)]
      congr 2
    have len : s.data.regs.rsp.toNat + 8 - (v.data.regs.rsp.toNat + 48) = frameSize v4 + 56 := by
      rw [vspNat]
      show s.data.regs.rsp.toBitVec.toNat + 8 - _ = _
      omega
    have hy' : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48)) (frameSize v4 + 56) y := by
      rw [← base, ← len]
      exact hy
    refine (frameX y (fun h => ?_)).symm
    have inWindow : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
        (insertWindow + A.depth + 8) y := below_sub _ _ _ _ _ (by omega) (by omega) y hy'
    rcases classify y h with heap | low | cw
    · exact trunk.sep.heapStack y heap.1 inWindow
    · rw [lowBase] at low
      exact below_under _ (frameSize v4 + 48) (frameSize v4 + 56) (frameSize v4 + 104) 56 (by omega)
        (by omega) (by omega) y hy' low
    · exact trunk.sep.bytesStack y (writes_bytes cw) inWindow
  · obtain ⟨before,atEntry,atV⟩ := mid.seqAdvanced trunk v.pc
    refine ⟨before,atEntry,?_⟩
    rw [← readNat_frame (before := v) (after := x) frameX _ 8 (fun y inside h => by
      have heap : L.Heap y := ⟨(L.table+AllowedipsMutationLayout.seq,8),
        by simp [Layout.heap, Layout.fixed, tableFields],inside⟩
      rcases classify y h with written | low | cw
      · exact written.2.1 inside
      · exact (trunk.heapWide y heap).1 (lowWide y low)
      · exact (trunk.heapWide y heap).2 cw)]
    exact atV
  · obtain ⟨d',device',same⟩ := after
    have deviceEq := child_device (bump d) p key cidr (if v4 then 32 else 128) pid parentNode owner
      hasParent hasPeer different
    have relatedX' := relatedX
    have shapeX' := shapeX
    rw [mid.rbp] at relatedX' shapeX'
    have live' : (names.allocated word.toNat).trie.nodes.map (·.2) =
        names.trie.nodes.map (·.2) ++ [word.toNat] := by
      simp [Names.allocated]
    refine ⟨names.allocated word.toNat,rest,trunk.table,trunk.peers,?_,armedAfter,recordsAfter,
      fun record' member => trunk.sites record' (pending ▸ List.mem_cons_of_mem _ member),
      trunk.objectsApart,object.inArena trunk,?_⟩
    · apply assertAt_of_related device'
      · show Allowedips.reconstruct (names.allocated word.toNat) Root.nodeOffsets x.data.dmem =
          .ok (Allowedips.target d')
        rw [same, deviceEq]
        exact relatedX'
      · rw [same, deviceEq]
        exact shapeX'
    · rw [live']
      apply premises.allocator.frame v.data.dmem x.data.dmem _ _ idle
      intro y arena notKept
      refine frameX y (fun h => ?_)
      rcases classify y h with heap | low | cw
      · exact notKept (heap.2.2 arena)
      · exact (trunk.heapWide y (arena_heap y arena)).1 (lowWide y low)
      · exact (trunk.heapWide y (arena_heap y arena)).2 cw
end

#print axioms child_body
end C1Trunk
