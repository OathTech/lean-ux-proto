import C1TrunkReach
/-! Result C1, package 2: the allocation call inside `add`, through
`AllocRule`: the rule's hypotheses from `Trunk` and a live state of `add`'s
frame, and what its conclusion gives back (the write frame below the
service's return word, the relation by the protected bytes). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem root_span {names : Allowedips.Names} (v4 : Bool) :
    (names.table+(if (if v4 then 32 else 128) = 32 then 0 else 8),8) ∈ readSpans names Root.nodeOffsets := by
  cases v4 <;>
    simp [readSpans,tableFields,AllowedipsMutationLayout.root4,AllowedipsMutationLayout.root6]

/-- The allocator's entry, reached from a live state `u` of `add`'s frame by
the CALL whose return site is `add+offset`. -/
structure AtAlloc (L : Statements.C1.Layout) (c : Context) (a u : MachineData) (e : MachineState)
    (offset : Nat) : Prop where
  live : Live c a u
  regs : e.data.regs = {u.regs with rsi := 3520, rdi := .ofBitVec (BitVec.ofNat 64 L.cache), rsp := u.regs.rsp-8}
  mem : e.data.dmem = Placement.callMemory u offset
  pc : e.pc = allocEntry
  mapped : ∀ x n, (a.dmem.loadInt x n).isSome = true → (e.data.dmem.loadInt x n).isSome = true
  forward : e.data.system.bits[10] = a.system.bits[10]

theorem range_split (sp : BitVec 64) (W k : Nat) (le : k ≤ W) (x : BitVec 64)
    (h : InRange (sp - .ofNat 64 W) W x) :
    InRange (sp - .ofNat 64 W) (W-k) x ∨ InRange (sp - .ofNat 64 k) k x := by
  obtain ⟨i,hi,eq⟩ := h
  by_cases low : i < W-k
  · exact .inl ⟨i,low,eq⟩
  · refine .inr ⟨i-(W-k),by omega,?_⟩
    rw [eq, sub_add_ofNat sp W i (by omega), sub_add_ofNat sp k (i-(W-k)) (by omega)]
    congr 2
    omega

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a u : MachineData} {e : MachineState} {offset : Nat}

/-- The stack pointer at the allocator's entry. -/
theorem AtAlloc.stackAt (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtAlloc L c a u e offset) :
    e.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104) := by
  rw [at'.regs]
  show (u.regs.rsp - 8).toBitVec = _
  rw [at'.live.stack]
  show a.regs.rsp.toBitVec - 96#64 - 8#64 = _
  rw [trunk.atAdd.stackAt]
  show _ - BitVec.ofNat 64 96 - BitVec.ofNat 64 8 = _
  rw [sub_sub_ofNat, sub_sub_ofNat]

/-- Everything written between the insertion's entry and the allocator's. -/
theorem AtAlloc.fromAdd (at' : AtAlloc L c a u e offset) :
    EqualOutside (fun x => Window a x ∨ c.writes x) a.dmem e.data.dmem := by
  rw [at'.mem]
  intro x outside
  refine (at'.live.fromEntry x outside).trans
    (storeInt_frame u.dmem (u.regs.rsp.toBitVec-8) 8 _ x (fun h => outside (.inl ?_)))
  rw [call_word a u at'.live.stack] at h
  exact window_sub a 0 8 (by decide) x (by simpa using h)

theorem AtAlloc.flight (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtAlloc L c a u e offset) : InFlight L A c s e := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room := trunk.sep.room
  have stackAt := at'.stackAt trunk
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := room
  have value : e.data.regs.rsp.toNat = s.data.regs.rsp.toNat - (frameSize v4 + 104) := by
    show e.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toBitVec.toNat - _
    rw [stackAt]
    exact toNat_sub_ofNat _ _ (by omega)
  have tight := window_tight trunk.atAdd (insertWindow + A.depth) wide
  refine ⟨by rw [value]; unfold insertWindow; omega,by rw [value]; omega,?_,
    fun x n h => at'.mapped x n (trunk.mapped x n h),at'.forward.trans trunk.forwardA,?_⟩
  · intro x hx
    refine (trunk.atAdd.frameAt x (fun h => hx ?_)).trans (at'.fromAdd x (fun h => hx ?_))
    · rcases h with h | h | h
      · exact .inl (below_sub _ _ _ _ _ (by omega) (by omega) x h)
      · exact .inr (.inr (seq_heap _ trunk.tableReg x h))
      · exact .inr (.inl h)
    · rcases h with h | h
      · exact .inl (range_mono _ _ _ (by omega) x (tight x h))
      · exact .inr (.inl h)
  · rw [at'.mem]
    exact state_frame c u.dmem _ at'.live.ready.state _
      (storeInt_frame u.dmem (u.regs.rsp.toBitVec-8) 8 _) at'.live.ready.pushSeparate

/-- The allocation call through `AllocRule`. -/
theorem AtAlloc.call (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtAlloc L c a u e offset)
    (live : List Nat) (liveArena : ∀ node ∈ live, InArena L node)
    (record : HiddenRecord) (rest : List HiddenRecord)
    (back : UInt64) (site : back = (Add.entry+.ofNat offset).toUInt64)
    (recorded : (back.toNat, record.site) ∈ allocSites)
    (idle : A.Idle e.data.dmem live (record :: rest)) :
    Eventually (instructionStep fetch) (fun t =>
      Returned e t back ∧ AllocResult L A live record rest t ∧
      InFlight L A c s t ∧
      ∀ x, Protected L s e live x → t.data.dmem.get? x = e.data.dmem.get? x) e := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room := trunk.sep.room
  have flight := at'.flight trunk
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := room
  have value : e.data.regs.rsp.toNat = s.data.regs.rsp.toNat - (frameSize v4 + 104) := by
    show e.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toBitVec.toNat - _
    rw [at'.stackAt trunk]
    exact toNat_sub_ofNat _ _ (by omega)
  have entryFrame : EntryFrame e (Add.entry+.ofNat offset).toUInt64 := by
    simpa only [EntryFrame,at'.regs,at'.mem,calledState,Placement.callMemory] using
      called_entry u (Add.entry+.ofNat offset) (.ofNat 0xffffffff81196d20) at'.live.ready.aligned
  have cacheValue := (trunk.cacheAt).2.1
  have flags : e.data.regs.get (.low .rsi .W32) = 0xdc0#32 := by
    simp [at'.regs,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  have depth : e.data.regs.rsp.toNat + 8 ≤ s.data.regs.rsp.toNat := by rw [value]; omega
  have cacheReg : e.data.regs.rdi.toNat = L.cache := by rw [at'.regs]; exact cacheValue
  have apart : spansApart (objectsOf L) L.arena = true := trunk.objectsApart
  have entryFrame' : EntryFrame e back := site ▸ entryFrame
  exact alloc fetch L A premises c s e family key cidr pid ra back live record rest ready apart
    liveArena flight depth at'.pc entryFrame' cacheReg flags recorded idle

/-- What the service wrote, as a frame: below its return word, the coverage
buffer, the heap. -/
theorem alloc_frame (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {t : MachineState} {live : List Nat} (k : Nat) (le : k ≤ insertWindow + A.depth)
    (stackAt : e.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 k)
    (before : InFlight L A c s e) (after : InFlight L A c s t)
    (kept : ∀ x, Protected L s e live x → t.data.dmem.get? x = e.data.dmem.get? x) :
    EqualOutside (fun x =>
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth - k) x ∨
      c.writes x ∨ L.Heap x) e.data.dmem t.data.dmem := by
  have room := trunk.sep.room
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := room
  have value : e.data.regs.rsp.toNat = s.data.regs.rsp.toNat - k := by
    show e.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toBitVec.toNat - _
    rw [stackAt]
    exact toNat_sub_ofNat _ _ (by omega)
  intro x hx
  by_cases live' : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 k) k x
  · refine (kept x (.inl ?_)).symm
    rw [stackAt, value]
    exact range_mono _ _ _ (by omega) x live'
  · have outside : ¬InsertWrites L A c s x := by
      intro h
      rcases h with h | h | h
      · rcases range_split _ _ k le x h with low | high
        · exact hx (.inl low)
        · exact live' high
      · exact hx (.inr (.inl h))
      · exact hx (.inr (.inr h))
    exact (before.frame x outside).symm.trans (after.frame x outside)

/-- The protected bytes carry the relation across a service call. -/
theorem protected_related (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    {t : MachineState} {d' : Device}
    (kept : ∀ x, Protected L s e (names.trie.nodes.map (·.2)) x →
      t.data.dmem.get? x = e.data.dmem.get? x)
    (related : Allowedips.Corresponds names Root.nodeOffsets e.data.dmem d')
    (shape : Allowedips.heap names (Allowedips.target d') e.data.dmem = .ok ()) :
    Allowedips.Corresponds names Root.nodeOffsets t.data.dmem d' ∧
    Allowedips.heap names (Allowedips.target d') t.data.dmem = .ok () := by
  have same : EqualOutside (fun x => ¬Protected L s e (names.trie.nodes.map (·.2)) x)
      e.data.dmem t.data.dmem := fun x hx => (kept x (Classical.not_not.mp hx)).symm
  have apart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ x, span.contains x →
      ¬¬Protected L s e (names.trie.nodes.map (·.2)) x := by
    intro span member x inside
    apply not_not_intro
    simp only [readSpans, List.mem_append] at member
    rcases member with tableField | nodeField | peerField
    · rw [table] at tableField
      exact .inr (.inl ⟨span,List.mem_append_left _ tableField,inside⟩)
    · obtain ⟨node,named,field⟩ := List.mem_flatMap.mp nodeField
      obtain ⟨slot,present,equal⟩ := List.mem_map.mp field
      have fits := nodeFields_inside slot present
      subst equal
      exact .inr (.inr (.inl ⟨node.2,List.mem_map.mpr ⟨node,named,rfl⟩,
        span_within _ _ _ _ (by omega) (by unfold nodeSize; omega) x inside⟩))
    · rw [peers] at peerField
      exact .inr (.inl ⟨span,List.mem_append_right _ peerField,inside⟩)
  refine ⟨(reconstruct_frame names Root.nodeOffsets same apart).symm.trans related,?_⟩
  exact (heap_frame names Root.nodeOffsets _ same
    (fun span member => apart span (metadata_read member))).symm.trans shape
end

#print axioms AtAlloc.call
#print axioms alloc_frame
#print axioms protected_related
end C1Trunk
