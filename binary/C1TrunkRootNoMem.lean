import C1TrunkAlloc
/-! Result C1, package 2: the empty root. `add` from its entry to the
allocator's entry, and the path on which the service returns NULL
(`-ENOMEM`, nothing changed but the sequence word). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- Empty root: `add`'s entry to the allocator's entry (the CALL at +0x42d). -/
theorem root_reach (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128))
    (empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none) :
    Eventually (instructionStep fetch) (fun e => ∃ u, AtAlloc L c a u e 0x432) ⟨a,Add.entry⟩ := by
  have r := trunk.resources
  obtain ⟨cacheLoad,_,cacheApart⟩ := trunk.cacheAt
  have slotAt := trunk.slotAt
  have rootWord : a.dmem.loadInt a.regs.rdi.toBitVec 8 = some 0 := by
    rw [slotAt]
    apply root_word trunk.relatedA
    cases v4 <;> simpa [bump] using empty
  have rootApart : ∀ x, InRange a.regs.rdi.toBitVec 8 x → ¬Window a x ∧ ¬c.writes x := by
    intro x h
    rw [slotAt] at h
    exact trunk.heapOutside x
      (read_heap trunk.table trunk.peers trunk.inArena _ (root_span v4) x h)
  have peer : a.regs.r8.toBitVec ≠ 0 := by
    rw [trunk.atAdd.peer]
    intro zero
    apply trunk.peerNonNull
    show s.data.regs.rcx.toBitVec.toNat = 0
    rw [zero]
    rfl
  have small : (if v4 then 32 else 128) < 256 := by cases v4 <;> decide
  have run := to_allocation fetch premises.insertion premises.tracePc premises.cmp1 r
    (if v4 then 32 else 128) cidr trunk.atAdd.bits (trunk.atAdd.cidr.trans trunk.cidr) bound small
    peer rootWord rootApart (BitVec.ofNat 64 L.cache) cacheLoad cacheApart
  have run' := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch run)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run'
  rintro e ⟨⟨⟨u,live,regs,mem,pc⟩,mapped⟩,_,forward⟩
  exact ⟨u,live,regs,mem,pc,mapped,forward⟩
end

theorem eax_nomem (r : Reg64s) (h : r.rax = 0xfffffff4) :
    r.get (.low .rax .W32) = BitVec.ofInt 32 (-ENOMEM) := by
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, h, ENOMEM]
  decide

theorem step_rootNoMem {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .rootNoMem) :
    cidr ≤ (if family == 4 then 32 else 128) ∧
    (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none ∧
    outcomes.head? ≠ some true ∧
    step d family key cidr pid placed exact outcomes = ⟨.rootNoMem,-ENOMEM,bump d,1⟩ := by
  by_cases long : cidr > (if family == 4 then 32 else 128)
  · simp only [step, long, ↓reduceIte] at hc
    cases hc
  · have slot : slotOf (bump d) (if family == 4 then Slot.root4 else Slot.root6) =
        (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) := by
      by_cases four : (family == 4) = true <;> simp [four, slotOf, bump]
    unfold step at hc ⊢
    simp only [long, ↓reduceIte, slot] at hc ⊢
    cases root : (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) with
    | some rootId =>
      exfalso
      simp only [root] at hc
      repeat' split at hc
      all_goals first | cases hc | simp at hc
    | none =>
      simp only [root] at hc ⊢
      cases outcomes with
      | nil => refine ⟨by omega,?_,?_,?_⟩ <;> first | trivial | rfl | simp
      | cons outcome rest =>
        cases outcome
        · refine ⟨by omega,?_,?_,?_⟩ <;> first | trivial | rfl | simp
        · cases hc

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w w' : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- The relation at the allocator's entry. -/
theorem AtAlloc.related (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {u : MachineData} {e : MachineState} {offset : Nat} (at' : AtAlloc L c a u e offset) :
    Allowedips.Corresponds names Root.nodeOffsets e.data.dmem (bump d) ∧
    Allowedips.heap names (Allowedips.target (bump d)) e.data.dmem = .ok () := by
  have apart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ x, span.contains x →
      ¬(Window a x ∨ c.writes x) := by
    intro span member x inside h
    have out := trunk.heapOutside x (read_heap trunk.table trunk.peers trunk.inArena span member x inside)
    exact h.elim out.1 out.2
  refine ⟨(reconstruct_frame names Root.nodeOffsets at'.fromAdd apart).symm.trans trunk.relatedA,?_⟩
  exact (heap_frame names Root.nodeOffsets _ at'.fromAdd
    (fun span member => apart span (metadata_read member))).symm.trans trunk.shapeA

/-- The allocator's state at its entry. -/
theorem AtAlloc.idle (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {u : MachineData} {e : MachineState} {offset : Nat} (at' : AtAlloc L c a u e offset) :
    A.Idle e.data.dmem (names.trie.nodes.map (·.2)) stream := by
  have fs := frameSize_range v4
  have wide := window_wide A
  apply trunk.idleFrame premises
  intro x hx
  refine (trunk.atAdd.frameAt x (fun h => hx ?_)).trans (at'.fromAdd x (fun h => hx ?_))
  · rcases h with h | h | h
    · exact .inl (below_sub _ _ _ _ _ (by omega) (by omega) x h)
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rcases h with h | h
    · exact .inl (range_mono _ _ _ (by omega) x (window_tight trunk.atAdd _ wide x h))
    · exact .inr (.inr h)

theorem Trunk.liveArena (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a) :
    ∀ node ∈ names.trie.nodes.map (·.2), InArena L node := by
  intro node member
  obtain ⟨named,isNode,rfl⟩ := List.mem_map.mp member
  exact trunk.inArena named isNode

/-- Empty root, the service returns NULL: `add` from entry to return. -/
theorem rootNoMem_body (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128))
    (empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none)
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 77) (failed : record.bytes.head? = some 0)
    (after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target (bump d))
    (recordsAfter : w'.ambient.hidden = some rest) (armedAfter : armed w' = true) :
    Eventually (instructionStep fetch) (AddPost L A c s w' v4 (-ENOMEM) seq a) ⟨a,Add.entry⟩ := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have r := trunk.resources
  have tight := window_tight trunk.atAdd (insertWindow + A.depth) wide
  apply eventually_trans (instructionStep fetch) _ _ _ (root_reach premises trunk bound empty)
  rintro e ⟨u,at'⟩
  have flightE := at'.flight trunk
  have stackE := at'.stackAt trunk
  have idleE : A.Idle e.data.dmem (names.trie.nodes.map (·.2)) (record :: rest) :=
    pending ▸ at'.idle premises trunk
  have recorded : ((Add.entry+.ofNat 0x432).toUInt64.toNat, record.site) ∈ allocSites := by
    rw [recordSite]
    decide
  apply eventually_trans (instructionStep fetch) _ _ _
    (at'.call alloc premises ready trunk _ trunk.liveArena record rest _ rfl recorded idleE)
  rintro t1 ⟨returned,result,flightT,kept⟩
  obtain ⟨pc1,sp1,_,_,_,_,_,_⟩ := returned
  have outcome : t1.data.regs.rax.toNat = 0 ∧
      A.Idle t1.data.dmem (names.trie.nodes.map (·.2)) rest := result.1 failed
  have null : t1.data.regs.rax.toBitVec = 0 := BitVec.eq_of_toNat_eq outcome.1
  have sp1' : t1.data.regs.rsp = u.regs.rsp := by
    rw [sp1, at'.regs]
    exact UInt64.sub_add_cancel _ _
  have pc1' : t1.pc = Add.entry+0x432 := pc1
  rw [Placement.at_pc t1 _ pc1']
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r432_layout.agreement premises.insertion.add) t1.data _ (alloc_result t1.data))
  rintro b ⟨regsB,memB,pcB⟩
  rw [ite_eq_left null] at pcB
  rw [Placement.at_pc b _ pcB]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r692_layout.agreement premises.insertion.add) b.data _ (nomem_code b.data))
  rintro x ⟨regsX,memX,pcX⟩
  have memXT : x.data.dmem = t1.data.dmem := memX.trans memB
  have spXU : x.data.regs.rsp = u.regs.rsp := by rw [regsX, regsB]; exact sp1'
  have spX : x.data.regs.rsp = a.regs.rsp - 96 := spXU.trans at'.live.stack
  have word := call_word a u at'.live.stack
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have valueE : s.data.regs.rsp.toNat + 8 - e.data.regs.rsp.toNat = frameSize v4 + 104 + 8 := by
    show s.data.regs.rsp.toBitVec.toNat + 8 - e.data.regs.rsp.toBitVec.toNat = _
    rw [stackE, toNat_sub_ofNat _ _ (by omega)]
    omega
  have wordE : e.data.regs.rsp.toBitVec = a.regs.rsp.toBitVec - 104 := by
    rw [at'.regs]
    exact word
  have keptFrame : EqualOutside (fun y => ¬Protected L s e (names.trie.nodes.map (·.2)) y)
      e.data.dmem t1.data.dmem := fun y hy => (kept y (Classical.not_not.mp hy)).symm
  have readyX : CallsReady c x.data := by
    refine ⟨memXT ▸ flightT.coverage,by rw [spXU]; exact at'.live.ready.aligned,?_,
      by rw [spXU]; exact at'.live.ready.pushSeparate,by rw [spXU]; exact at'.live.ready.returnSeparate,
      at'.live.ready.metadataSeparate,at'.live.ready.preemptSeparate⟩
    rw [memXT, spXU]
    apply flightT.mapped
    have at'' : u.regs.rsp.toBitVec - 8 = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104) := by
      rw [← stackE, at'.regs]
      rfl
    rw [at'']
    exact trunk.caller.below.load _ 8 (by omega) (by omega)
  have loadX : ∀ off n : Nat, 8 ≤ off → off+n ≤ 112 →
      x.data.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n =
        (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n := by
    intro off n lo hi
    rw [memXT, ← keptFrame.loadInt _ n (fun i hi' h => h (.inl (by
      rw [wordE, valueE]
      exact ⟨off+i,by omega,by rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩))), at'.mem]
    have skip := (storeInt_frame u.dmem (u.regs.rsp.toBitVec-8) 8
      (Add.entry+.ofNat 0x432).toBitVec.toInt).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n
      (fun i hi' h => by
        rw [word] at h
        exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) off n 0 8 (by omega) (by omega)
          (.inr (by omega)) _ ⟨i,hi',rfl⟩ (by simpa using h))
    exact skip.symm.trans (at'.live.window_load r off n lo hi)
  obtain ⟨relatedE,shapeE⟩ := at'.related trunk
  obtain ⟨relatedT,shapeT⟩ := protected_related trunk.table trunk.peers kept relatedE shapeE
  have heapOut := trunk.heapOutside
  have projection : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ y, span.contains y →
      ¬Window a y ∧ ¬c.writes y := fun span member y inside =>
    heapOut y (read_heap trunk.table trunk.peers trunk.inArena span member y inside)
  rw [Placement.at_pc x _ pcX]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (finish_tail fetch premises.insertion premises.tracePc r trunk.atAdd.returnWord readyX spX loadX
      (memXT ▸ relatedT) (memXT ▸ shapeT) projection)
  rintro f ⟨pcF,raxF,rspF,rbxF,rbpF,r12F,r13F,r14F,r15F,_,relatedF,shapeF,frameF⟩
  have seqHeap (i : Nat) (hi' : i < 8) :
      L.Heap (BitVec.ofNat 64 (L.table+AllowedipsMutationLayout.seq) + .ofNat 64 i) :=
    ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.heap, Layout.fixed, tableFields],⟨i,hi',rfl⟩⟩
  refine ⟨⟨pcF,rspF,rbxF,rbpF,r12F,r13F,r14F,r15F⟩,?_,?_,?_,?_⟩
  · apply eax_nomem
    rw [raxF, regsX]
    rfl
  · rw [← frameF.loadInt _ 8 (fun i hi' h => h.elim (heapOut _ (seqHeap i hi')).1 (heapOut _ (seqHeap i hi')).2),
      memXT, ← keptFrame.loadInt _ 8 (fun i hi' h => h (.inr (.inl
        ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.fixed, tableFields],⟨i,hi',rfl⟩⟩))),
      ← at'.fromAdd.loadInt _ 8 (fun i hi' h =>
        h.elim (heapOut _ (seqHeap i hi')).1 (heapOut _ (seqHeap i hi')).2),
      ← seq_address _ L.table trunk.tableReg]
    exact trunk.atAdd.seqWord
  · obtain ⟨d',device',same⟩ := after
    refine ⟨names,rest,trunk.table,trunk.peers,?_,armedAfter,recordsAfter,
      fun record' member => trunk.sites record' (pending ▸ List.mem_cons_of_mem _ member),
      trunk.objectsApart,trunk.inArena,?_⟩
    · apply assertAt_of_related device'
      · show Allowedips.reconstruct names Root.nodeOffsets f.data.dmem = .ok (Allowedips.target d')
        rw [same]
        exact relatedF
      · rw [same]
        exact shapeF
    · apply premises.allocator.frame t1.data.dmem f.data.dmem _ _ outcome.2
      intro y arena _
      rw [← memXT]
      exact frameF y (fun h => h.elim (heapOut y (arena_heap y arena)).1 (heapOut y (arena_heap y arena)).2)
  · intro y hy
    have service := alloc_frame trunk (frameSize v4 + 104) (by omega) stackE flightE flightT kept
    refine (at'.fromAdd y (fun h => hy ?_)).trans ((service y (fun h => hy ?_)).trans
      (memXT ▸ frameF y (fun h => hy ?_)))
    · rcases h with h | h
      · exact .inl (tight y h)
      · exact .inr (.inl h)
    · rcases h with h | h | h
      · exact .inl (range_mono _ _ _ (by omega) y h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rcases h with h | h
      · exact .inl (tight y h)
      · exact .inr (.inl h)
end

#print axioms root_reach
#print axioms step_rootNoMem
#print axioms rootNoMem_body
end C1Trunk
