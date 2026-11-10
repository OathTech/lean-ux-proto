import C1TrunkNodeNoMem
import C1TrunkSourceExact
import AllowedipsExactTotal
import PairCallRelation
/-! Result C1, package 2: the exact match. From the placement loop's exact
exit (`+0x3ca`) through the owner reload and two callbacks to `+0x3e5`, the
landed `Exact.assignment_from_relation` to the common exit, and the finish
through `Exits`. The landed segment's writes (the node's owner word and list
links) are shown to lie in the heap, apart from the sequence word and inside
the arena only within named nodes. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- A resolved identity is a named pair. -/
theorem address_mem {names : List (Nat × Nat)} {id a : Nat}
    (h : Trie.address names (some id) = .ok a) : (id,a) ∈ names := by
  simp only [Trie.address] at h
  cases found : names.find? (·.1 == id) with
  | none => rw [found] at h; cases h
  | some pair =>
    obtain ⟨p1,p2⟩ := pair
    rw [found] at h
    have e1 : p1 = id := by
      have h' := List.find?_some found
      simpa using h'
    have e2 : p2 = a := Except.ok.inj h
    have member := List.mem_of_find?_eq_some found
    rw [← e1, ← e2]
    exact member

/-- A named peer is a peer of the related device (after the landed `Trie.node_peer_present`). -/
theorem peer_present {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    (related : Allowedips.Corresponds names o m d) {pid base : Nat}
    (named : (pid,base) ∈ names.trie.peers) : ∃ owner, d.peers.get? pid = some owner := by
  have fields := Trie.reconstruct_fields related.trie
  obtain ⟨⟨pid',count⟩,member,equal,_⟩ := fields.peers.left (pid,base) named
  obtain ⟨⟨id',peer⟩,source,value⟩ := List.mem_map.mp member
  have same : id' = pid := (Prod.mk.inj value).1.trans equal.symm
  subst same
  exact ⟨peer,Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp source⟩

/-- The exact segment's register effect keeps the stack pointer and clears `rbx`. -/
theorem exact_effect_regs {q : MachineData} {memory : DataMem} {regs : Reg64s}
    (h : Exact.effect q = .ok (memory,regs)) : regs.rsp = q.regs.rsp ∧ regs.rbx = 0 := by
  unfold Exact.effect at h
  obtain ⟨⟨m1,r1⟩,removed,appended⟩ := bind_ok h
  have first : r1.rsp = q.regs.rsp := by
    unfold Exact.removeEffect at removed
    obtain ⟨_,_,removed⟩ := bind_ok removed
    obtain ⟨_,_,removed⟩ := bind_ok removed
    obtain ⟨_,_,removed⟩ := bind_ok removed
    obtain ⟨_,_,removed⟩ := bind_ok removed
    obtain ⟨_,_,removed⟩ := bind_ok removed
    obtain ⟨_,_,removed⟩ := bind_ok removed
    have eq := Except.ok.inj removed
    rw [← (Prod.mk.inj eq).2]
  unfold Exact.appendEffect at appended
  obtain ⟨_,_,appended⟩ := bind_ok appended
  obtain ⟨_,_,appended⟩ := bind_ok appended
  obtain ⟨_,_,appended⟩ := bind_ok appended
  obtain ⟨_,_,appended⟩ := bind_ok appended
  have eq := Except.ok.inj appended
  rw [← (Prod.mk.inj eq).2]
  exact ⟨first,rfl⟩

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w w' : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- The exact segment's writes: in the heap, apart from the sequence word,
and inside the arena only within a named node. -/
theorem exact_writes (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {id base : Nat} (named : (id,base) ∈ names.trie.nodes) (x : BitVec 64)
    (h : Exact.Writes names base x) :
    L.Heap x ∧ ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 x ∧
    (L.Arena x → Kept (names.trie.nodes.map (·.2)) x) := by
  have valid := related_valid trunk.relatedA
  obtain ⟨tableTop,tableApart⟩ := Root.table_valid_geometry valid
  have tableEq : names.table = L.table := trunk.table
  rw [tableEq] at tableTop tableApart
  have trieValid : Trie.validate names.trie Root.nodeOffsets = .ok () := by
    unfold validate at valid
    obtain ⟨_,trieValid,_⟩ := bind_ok valid
    exact trieValid
  have ranges := trie_validate_ranges trieValid
  have seqValue : AllowedipsMutationLayout.seq = 16 := rfl
  have nodeCase (node : Nat × Nat) (isNode : node ∈ names.trie.nodes) (off size : Nat)
      (fits : off + size ≤ 72) (inside : InRange (.ofNat 64 (node.2+off)) size x) :
      L.Heap x ∧ ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 x ∧
      (L.Arena x → Kept (names.trie.nodes.map (·.2)) x) := by
    obtain ⟨home,isArena,low,high⟩ := trunk.inArena node isNode
    unfold nodeSize at high
    have arena : L.Arena x := ⟨home,isArena,span_within _ _ _ _ (by omega) (by omega) x inside⟩
    exact ⟨arena_heap x arena,arena_not_seq trunk.objectsApart x arena,fun _ =>
      ⟨node.2,List.mem_map.mpr ⟨node,isNode,rfl⟩,
        span_within _ _ _ _ (by omega) (by unfold nodeSize; omega) x inside⟩⟩
  rcases h with word | ⟨link,slot,offset,which,inside⟩
  · exact nodeCase (id,base) named 0 8 (by omega) (by simpa using word)
  · have within : InRange (.ofNat 64 link) 16 x := by
      obtain ⟨i,bound,equal⟩ := inside
      refine ⟨offset+i,by rcases which with rfl|rfl <;> omega,?_⟩
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal
    cases slot with
    | node isNode => exact nodeCase _ isNode 56 16 (by omega) within
    | @peer pid' pbase isPeer =>
      have allocation : (pbase,Layouts.peerSize) ∈ allocations names Root.nodeOffsets :=
        List.mem_append_right _ (List.mem_map.mpr ⟨(pid',pbase),isPeer,rfl⟩)
      have bound := (ranges _ allocation).2
      have apart := tableApart _ allocation
      have size : Layouts.peerSize = 1520 := rfl
      simp only [disjointRanges, Bool.or_eq_true, decide_eq_true_eq, size] at apart bound
      have isPeer' : (pid',pbase) ∈ L.peers := trunk.peers ▸ isPeer
      refine ⟨?_,fun seqAt => ?_,fun arena => ?_⟩
      · obtain ⟨i,hi,eq⟩ := within
        by_cases first : i < 8
        · exact ⟨(pbase+1096,8),List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨(pid',pbase),isPeer',List.mem_map.mpr ⟨(1096,8),by decide,rfl⟩⟩)),
            ⟨i,first,eq⟩⟩
        · refine ⟨(pbase+1104,8),List.mem_append_left _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨(pid',pbase),isPeer',List.mem_map.mpr ⟨(1104,8),by decide,rfl⟩⟩)),
            ⟨i-8,by omega,?_⟩⟩
          rw [eq, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
          congr 1
          show pbase + 1096 + i = pbase + 1104 + (i - 8)
          omega
      · exact nat_apart (pbase+1096,16) (L.table+AllowedipsMutationLayout.seq,8)
          (by show pbase+1096+16 ≤ 2^64; omega) (by simp only [seqValue]; omega)
          (by show pbase+1096+16 ≤ L.table+AllowedipsMutationLayout.seq ∨
                L.table+AllowedipsMutationLayout.seq+8 ≤ pbase+1096
              simp only [seqValue]; omega) x within seqAt
      · exact absurd arena (arena_not_object trunk.objectsApart (pbase,Layouts.peerSize)
          (List.mem_append_right _ (List.mem_map.mpr ⟨(pid',pbase),isPeer',rfl⟩)) x
          (span_within _ _ _ _ (by omega) (by show pbase+1096+16 ≤ pbase+1520; omega) x within))

/-- The loop's exact exit to +0x3e5: the owner reloaded, two callbacks. -/
theorem exact_reach (premises : Premises fetch L A)
    {bits : Nat} {placed : Option NodeId} {t : MachineState}
    (walked : Walked c names d a bits placed true t) :
    Eventually (instructionStep fetch) (fun q => q.pc = Add.entry+0x3e5 ∧ Held c a q.data ∧
      q.data.regs.rbx = t.data.regs.rbx ∧ q.data.regs.r14 = a.regs.r8 ∧
      (∀ x n, (a.dmem.loadInt x n).isSome = true → (q.data.dmem.loadInt x n).isSome = true) ∧
      q.data.system.bits[10] = a.system.bits[10]) t := by
  have pcT : t.pc = Add.entry+0x3ca := by
    have h := walked.pc
    simpa using h
  have run : Eventually (instructionStep fetch) (fun q => q.pc = Add.entry+0x3e5 ∧ Held c a q.data ∧
      q.data.regs.rbx = t.data.regs.rbx ∧ q.data.regs.r14 = a.regs.r8) ⟨t.data,Add.entry+0x3ca⟩ := by
    obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp walked.held.ready.mapped
    have ownerWord : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+0x18) 8 =
        some (a.regs.r8.toBitVec.toNat : Int) := walked.owner
    have called := region_callback fetch (.ofNat 0xffffffff810f31f0) (Add.entry+0x3d4) .pc
      premises.callbacks.pc c ⟨t.data,Add.entry+0x3ca⟩ t.data
      {t.data.regs with r14 := .ofBitVec a.regs.r8.toBitVec} walked.held.ready
      (region_eventually (Add_r3ca_layout.agreement premises.insertion.add) t.data _
        (exact_owner t.data a.regs.r8.toBitVec old ownerWord mapped))
    apply eventually_trans (instructionStep fetch) _ _ _ called
    rintro t1 ⟨pc1,sp1,bx1,_,r12_1,r13_1,r14_1,_,ready1,frame1⟩
    have held1 := walked.held.next ready1 sp1 r12_1 r13_1 frame1
    rw [Placement.at_pc t1 _ pc1]
    obtain ⟨old1,mapped1⟩ := Option.isSome_iff_exists.mp held1.ready.mapped
    have called2 := region_callback fetch (.ofNat 0xffffffff810f40c0) (Add.entry+0x3e0) .constCmp1
      premises.callbacks.constCmp1 c ⟨t1.data,Add.entry+0x3d4⟩ t1.data
      {t1.data.regs with rsi := 1, rdi := 0} held1.ready
      (region_eventually (Add_r3d4_layout.agreement premises.insertion.add) t1.data _
        (exact_const_arguments t1.data old1 mapped1))
    apply eventually_trans (instructionStep fetch) _ _ _ called2
    rintro t2 ⟨pc2,sp2,bx2,_,r12_2,r13_2,r14_2,_,ready2,frame2⟩
    have held2 := held1.next ready2 sp2 r12_2 r13_2 frame2
    rw [Placement.at_pc t2 _ pc2]
    apply eventually_weaken (instructionStep fetch) _ _ _ _
      (held2.call fetch premises.tracePc (Add.entry+0x3e0) (premises.insertion.add _ _ (by rfl)))
    rintro t3 ⟨pc3,held3,bx3,_,r14_3,_⟩
    exact ⟨pc3,held3,bx3.trans (bx2.trans bx1),r14_3.trans (r14_2.trans r14_1)⟩
  have run' := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch run)
  rw [Placement.at_pc t _ pcT]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run'
  rintro q ⟨⟨⟨pcQ,held,bx,r14⟩,mapped⟩,_,forward⟩
  exact ⟨pcQ,held,bx,r14,fun x n h => mapped x n (walked.mapped x n h),forward.trans walked.forward⟩

/-- Exact match: `add` from its entry to the insertion's return. -/
theorem exact_body (framed : FramedHolds) (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128)) (keyBound : key < 2^(if v4 then 32 else 128))
    (rootId : NodeId)
    (rootAt : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId)
    (rootNode : ∃ node, (bump d).nodes.get? rootId = some node ∧ node.bitlen = (if v4 then 32 else 128))
    (id : NodeId) (n : AipNode) (hasNode : (bump d).nodes.get? id = some n)
    (ambient finalAmbient : Ambient) (finalStore : AipStore)
    (accepted : ((WG.nodePlacement (some rootId) key cidr (if v4 then 32 else 128)).run
      (Source.Aip.store (bump d))).run ambient = .ok (((some id,true),finalStore),finalAmbient))
    (after : ∃ d', w'.wg.dev = some d' ∧
      Allowedips.target d' = Allowedips.target (exactDevice (bump d) pid id n))
    (recordsAfter : w'.ambient.hidden = some stream) (armedAfter : armed w' = true) :
    Eventually (instructionStep fetch) (InsertPost L A c s w' ra 0) ⟨a,Add.entry⟩ := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have top' : s.data.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 := trunk.sep.top
  apply eventually_trans (instructionStep fetch) _ _ _
    (trunk_walked premises trunk bound keyBound rootId rootAt rootNode (some id) true
      ambient finalAmbient finalStore accepted)
  intro t walked
  apply eventually_trans (instructionStep fetch) _ _ _ (exact_reach premises walked)
  rintro q ⟨pcQ,held,bxQ,r14Q,mappedQ,forwardQ⟩
  obtain ⟨relatedQ,shapeQ⟩ := held.related trunk
  obtain ⟨_,namedAll⟩ := placed_address relatedQ (placed := some id)
    (fun id' eq => by cases eq; exact ⟨n,hasNode⟩) (bxQ.trans walked.rbx)
  have named := namedAll id rfl
  have peerNamed : (pid,s.data.regs.rcx.toNat) ∈ names.trie.peers := by
    rw [trunk.peers]
    exact address_mem trunk.peer
  obtain ⟨owner,hasPeer⟩ := peer_present relatedQ peerNamed
  have peerAt : q.data.regs.r14.toNat = s.data.regs.rcx.toNat := by
    rw [r14Q, trunk.atAdd.peer]
  obtain ⟨memory,regs,finalWG,finalAmbient',eff,sourceRun,exec⟩ :=
    Exact.assignment_from_relation fetch premises.insertion
      (k := {w.wg with dev := some (bump d)}) (ambient := w.ambient) rfl relatedQ shapeQ named hasNode
      peerNamed hasPeer rfl peerAt
  obtain ⟨regsSp,regsBx⟩ := exact_effect_regs eff
  have exec' := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch exec)
  rw [Placement.at_pc q _ pcQ]
  apply eventually_trans (instructionStep fetch) _ _ _ exec'
  rintro x ⟨⟨⟨pcX,regsX,memX,frameX,finalDevice,final,relatedX,shapeX⟩,mappedX⟩,_,forwardX⟩
  have deviceEq : finalDevice = exactDevice (bump d) pid id n :=
    exact_run_device _ finalWG (bump d) finalDevice w.ambient finalAmbient' id pid n owner rfl hasNode
      hasPeer sourceRun final
  subst deviceEq
  have writes (y : BitVec 64) (h : Exact.Writes names q.data.regs.rbx.toNat y) :=
    exact_writes trunk named y h
  have spX : x.data.regs.rsp = q.data.regs.rsp := by rw [regsX]; exact regsSp
  have qBV := held.stackAt trunk
  have qNat : q.data.regs.rsp.toNat = s.data.regs.rsp.toNat - (frameSize v4 + 96) := by
    show q.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toBitVec.toNat - _
    rw [qBV]
    exact toNat_sub_ofNat _ _ (by omega)
  have word := call_word a q.data held.stack
  have readyX : CallsReady c x.data := by
    refine ⟨?_,by rw [spX]; exact held.ready.aligned,?_,
      by rw [spX]; exact held.ready.pushSeparate,by rw [spX]; exact held.ready.returnSeparate,
      held.ready.metadataSeparate,held.ready.preemptSeparate⟩
    · exact state_frame c q.data.dmem x.data.dmem held.ready.state _ frameX
        (fun y read h => trunk.sep.heapBytes y (writes y h).1 read)
    · rw [spX, ← frameX.loadInt _ 8 (fun i hi h => (trunk.heapWide _ (writes _ h).1).1 (by
        rw [word]
        exact wide_sub a 0 8 (by decide) _ ⟨i,hi,by simp⟩))]
      exact held.ready.mapped
  have flightX : InFlight L A c s x := by
    refine ⟨by rw [spX, qNat]; unfold insertWindow; omega,by rw [spX, qNat]; omega,?_,
      fun y k h => mappedX y k (mappedQ y k (trunk.mapped y k h)),
      forwardX.trans (forwardQ.trans trunk.forwardA),readyX.state⟩
    intro y hy
    refine (trunk.atAdd.frameAt y (fun h => hy ?_)).trans
      ((held.fromEntry y (fun h => hy ?_)).trans (frameX y (fun h => hy ?_)))
    · rcases h with h | h | h
      · exact .inl (below_sub _ _ _ _ _ (by omega) (by omega) y h)
      · exact .inr (.inr (seq_heap _ trunk.tableReg y h))
      · exact .inr (.inl h)
    · rcases h with h | h
      · exact .inl (range_mono _ _ _ (by omega) y (wide_tight trunk.atAdd _ wide y h))
      · exact .inr (.inl h)
    · exact .inr (.inr (writes y h).1)
  have seqWordX : x.data.dmem.loadInt (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 =
      some ((1+seq).toNat : Int) := by
    rw [← frameX.loadInt _ 8 (fun i hi h => (writes _ h).2.1 ⟨i,hi,rfl⟩),
      held.outside_load _ 8 (fun y hy => trunk.heapWide y
        ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.heap, Layout.fixed, tableFields],hy⟩),
      ← seq_address _ L.table trunk.tableReg]
    exact trunk.atAdd.seqWord
  refine finish_exit (held.exits framed premises trunk (Add.entry+0x3e5)) pcX spX flightX readyX
    (fun y hy => ?_) (ebx_zero _ (by rw [regsX]; exact regsBx)) ?_ ?_
  · refine (frameX y (fun h => trunk.sep.heapStack y (writes y h).1 ?_)).symm
    have base : q.data.regs.rsp.toBitVec + 48 =
        s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48) := by
      rw [qBV]
      show _ + BitVec.ofNat 64 48 = _
      rw [sub_add_ofNat _ _ 48 (by omega)]
      congr 2
    have len : s.data.regs.rsp.toNat + 8 - (q.data.regs.rsp.toNat + 48) = frameSize v4 + 56 := by
      rw [qNat]
      show s.data.regs.rsp.toBitVec.toNat + 8 - (s.data.regs.rsp.toBitVec.toNat - _ + 48) = _
      omega
    have hy' : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 48)) (frameSize v4 + 56) y := by
      have h' : InRange (q.data.regs.rsp.toBitVec + 48)
          (s.data.regs.rsp.toNat + 8 - (q.data.regs.rsp.toNat + 48)) y := hy
      rw [base, len] at h'
      exact h'
    exact below_sub _ _ _ _ _ (by omega) (by omega) y hy'
  · have address := seq_address s.data.regs.rdi L.table trunk.tableReg
    refine ⟨seq.toNat,readNat_of_load ?_,readNat_of_load ?_⟩
    · rw [← address]
      exact trunk.caller.seqWord
    · rw [seqWordX]
      congr 2
      rw [BitVec.toNat_add]
      show (1 + seq.toNat) % 2^64 = (seq.toNat + 1) % 2^64
      rw [Nat.add_comm]
  · obtain ⟨d',device',same⟩ := after
    refine ⟨names,stream,trunk.table,trunk.peers,?_,armedAfter,recordsAfter,trunk.sites,
      trunk.objectsApart,trunk.inArena,?_⟩
    · apply assertAt_of_related device'
      · show Allowedips.reconstruct names Root.nodeOffsets x.data.dmem = .ok (Allowedips.target d')
        rw [same]
        exact relatedX
      · rw [same]
        exact shapeX
    · have idleQ : A.Idle q.data.dmem (names.trie.nodes.map (·.2)) stream := by
        apply trunk.idleFrame premises
        intro y hy
        refine (trunk.atAdd.frameAt y (fun h => hy ?_)).trans (held.fromEntry y (fun h => hy ?_))
        · rcases h with h | h | h
          · exact .inl (below_sub _ _ _ _ _ (by omega) (by omega) y h)
          · exact .inr (.inl h)
          · exact .inr (.inr h)
        · rcases h with h | h
          · exact .inl (range_mono _ _ _ (by omega) y (wide_tight trunk.atAdd _ wide y h))
          · exact .inr (.inr h)
      exact premises.allocator.frame q.data.dmem x.data.dmem _ _ idleQ
        (fun y arena notKept => frameX y (fun h => notKept ((writes y h).2.2 arena)))
end

/-- PACKAGE 2. Exact match. -/
theorem pathExact_proof : PathExact := by
  intro framed fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready _ facts hcase
  have rf := insertReady_facts ready
  have hcase' : (step d family key cidr pid placed exact
      (stream.map fun r => r.bytes.head? == some 1)).case = .exact := by
    rw [← facts.model]; exact hcase
  obtain ⟨isExact,stEq⟩ := step_exact hcase'
  obtain ⟨bound,rootId,rootAt⟩ := step_walked_of (.inl hcase')
  subst isExact
  obtain ⟨⟨ambient,finalAmbient,finalStore,accepted⟩,walkFact⟩ := facts.walked
    (by rw [hcase]; decide) (by rw [hcase]; decide) (by rw [hcase]; decide)
  obtain ⟨id,rfl⟩ : ∃ id, placed = some id := by
    cases placed with
    | none => exact absurd (walk_none walkFact) (by decide)
    | some id => exact ⟨id,rfl⟩
  obtain ⟨n,hasNode,_⟩ := walk_placed walkFact
  have stEq' : step d family key cidr pid (some id) true
      (stream.map fun r => r.bytes.head? == some 1) = ⟨.exact,0,exactDevice (bump d) pid id n,0⟩ := by
    rw [stEq]
    simp only [Option.bind_some, hasNode, Option.map_some]
  have answerEq : answer = 0 := by rw [facts.result, facts.model, stEq']
  have after : ∃ d', w'.wg.dev = some d' ∧
      Allowedips.target d' = Allowedips.target (exactDevice (bump d) pid id n) := by
    have h := facts.after
    rw [facts.model, stEq'] at h
    exact h
  have recordsAfter : w'.ambient.hidden = some stream := by
    have h := facts.recordsAfter
    rw [facts.model, stEq'] at h
    simpa using h
  have rootNode := ordered_root facts.trie rootAt
  rw [answerEq]
  rcases rf.families with rfl | rfl
  · exact to_trunk fetch L A premises c s w true key cidr pid ra inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = stream := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact exact_body framed premises trunk bound facts.keyBound rootId rootAt rootNode id n hasNode
          ambient finalAmbient finalStore
          (by rw [show rootOf d0 4 = some rootId from rootAt] at accepted; exact accepted)
          after recordsAfter facts.armedAfter)
  · exact to_trunk fetch L A premises c s w false key cidr pid ra inv
      rf.pc rf.table rf.peer rf.peerNonNull rf.cidr rf.key rf.cache rf.frame _
      (fun names stream0 d0 seq a trunk => by
        have hd : d0 = d := Option.some.inj (trunk.device.symm.trans facts.device)
        have hs : stream0 = stream := Option.some.inj (trunk.hidden.symm.trans facts.records)
        subst hd hs
        exact exact_body framed premises trunk bound facts.keyBound rootId rootAt rootNode id n hasNode
          ambient finalAmbient finalStore
          (by rw [show rootOf d0 6 = some rootId from rootAt] at accepted; exact accepted)
          after recordsAfter facts.armedAfter)

#print axioms exact_body
#print axioms pathExact_proof
end C1Trunk
