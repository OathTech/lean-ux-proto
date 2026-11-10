import C1TrunkWalked
/-! Result C1, package 2: the allocation at :205 on a nonempty root. From the
loop's other exit (`+0x120`) to the allocator's entry, through `AllocRule`,
and the store of the result at `+0x144`. `AtCall` is `AtAlloc` for a held
state; `Mid` is a state of `add`'s frame after the service returned (the
arena and the service's scratch have changed, so `Held` no longer applies). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- The allocator's entry, reached from a held state `u` of `add`'s frame by
the CALL whose return site is `add+offset` (after `AtAlloc`). -/
structure AtCall (L : Statements.C1.Layout) (c : Context) (a u : MachineData) (e : MachineState)
    (offset : Nat) : Prop where
  held : Held c a u
  regs : e.data.regs = {u.regs with rsi := 3520, rdi := .ofBitVec (BitVec.ofNat 64 L.cache), rsp := u.regs.rsp-8}
  mem : e.data.dmem = Placement.callMemory u offset
  pc : e.pc = allocEntry
  mapped : ∀ x n, (a.dmem.loadInt x n).isSome = true → (e.data.dmem.loadInt x n).isSome = true
  forward : e.data.system.bits[10] = a.system.bits[10]

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a u : MachineData} {e : MachineState} {offset : Nat}

/-- The `node_cache` word is outside `add`'s frame, the scratch and the coverage buffer. -/
theorem Trunk.cacheWide (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a) :
    ∀ x, InRange nodeCacheAddress 8 x → ¬Wide a x ∧ ¬c.writes x := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have word : nodeCacheAddress = .ofNat 64 cacheWord := by decide
  intro x h
  rw [word] at h
  exact ⟨fun hw => trunk.sep.stackCache x (range_mono _ _ _ (by omega) x
    (wide_tight trunk.atAdd _ wide x hw)) h,fun hw => trunk.sep.writesCache x hw h⟩

theorem AtCall.stackAt (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtCall L c a u e offset) :
    e.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104) := by
  rw [at'.regs]
  show (u.regs.rsp - 8).toBitVec = _
  rw [at'.held.stack]
  show a.regs.rsp.toBitVec - 96#64 - 8#64 = _
  rw [trunk.atAdd.stackAt]
  show _ - BitVec.ofNat 64 96 - BitVec.ofNat 64 8 = _
  rw [sub_sub_ofNat, sub_sub_ofNat]

theorem AtCall.fromAdd (at' : AtCall L c a u e offset) :
    EqualOutside (fun x => Wide a x ∨ c.writes x) a.dmem e.data.dmem := by
  rw [at'.mem]
  intro x outside
  refine (at'.held.fromEntry x outside).trans
    (storeInt_frame u.dmem (u.regs.rsp.toBitVec-8) 8 _ x (fun h => outside (.inl ?_)))
  rw [call_word a u at'.held.stack] at h
  exact wide_sub a 0 8 (by decide) x (by simpa using h)

theorem AtCall.flight (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtCall L c a u e offset) : InFlight L A c s e := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room := trunk.sep.room
  have stackAt := at'.stackAt trunk
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := room
  have value : e.data.regs.rsp.toNat = s.data.regs.rsp.toNat - (frameSize v4 + 104) := by
    show e.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toBitVec.toNat - _
    rw [stackAt]
    exact toNat_sub_ofNat _ _ (by omega)
  have tight := wide_tight trunk.atAdd (insertWindow + A.depth) wide
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
    exact state_frame c u.dmem _ at'.held.ready.state _
      (storeInt_frame u.dmem (u.regs.rsp.toBitVec-8) 8 _) at'.held.ready.pushSeparate

/-- The allocation call through `AllocRule`, from a held state. -/
theorem AtCall.call (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtCall L c a u e offset)
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
      called_entry u (Add.entry+.ofNat offset) (.ofNat 0xffffffff81196d20) at'.held.ready.aligned
  have cacheValue := (trunk.cacheAt).2.1
  have flags : e.data.regs.get (.low .rsi .W32) = 0xdc0#32 := by
    simp [at'.regs,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  have depth : e.data.regs.rsp.toNat + 8 ≤ s.data.regs.rsp.toNat := by rw [value]; omega
  have cacheReg : e.data.regs.rdi.toNat = L.cache := by rw [at'.regs]; exact cacheValue
  have apart : spansApart (objectsOf L) L.arena = true := trunk.objectsApart
  have entryFrame' : EntryFrame e back := site ▸ entryFrame
  exact alloc fetch L A premises c s e family key cidr pid ra back live record rest ready apart
    liveArena flight depth at'.pc entryFrame' cacheReg flags recorded idle

theorem AtCall.related (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtCall L c a u e offset) :
    Allowedips.Corresponds names Root.nodeOffsets e.data.dmem (bump d) ∧
    Allowedips.heap names (Allowedips.target (bump d)) e.data.dmem = .ok () := by
  have apart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ x, span.contains x →
      ¬(Wide a x ∨ c.writes x) := by
    intro span member x inside h
    have out := trunk.heapWide x (read_heap trunk.table trunk.peers trunk.inArena span member x inside)
    exact h.elim out.1 out.2
  refine ⟨(reconstruct_frame names Root.nodeOffsets at'.fromAdd apart).symm.trans trunk.relatedA,?_⟩
  exact (heap_frame names Root.nodeOffsets _ at'.fromAdd
    (fun span member => apart span (metadata_read member))).symm.trans trunk.shapeA

theorem AtCall.idle (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtCall L c a u e offset) :
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
    · exact .inl (range_mono _ _ _ (by omega) x (wide_tight trunk.atAdd _ wide x h))
    · exact .inr (.inr h)

/-- The loop's other exit to the allocator's entry (the CALL at +0x13f). -/
theorem node_reach (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {bits : Nat} {placed : Option NodeId} {t : MachineState}
    (walked : Walked c names d a bits placed false t) :
    Eventually (instructionStep fetch) (fun e => ∃ u, AtCall L c a u e 0x144 ∧
      u.regs.rbx = t.data.regs.rbx ∧ u.regs.rbp = t.data.regs.rbp ∧
      u.regs.r14 = t.data.regs.r14 ∧ u.regs.r15 = t.data.regs.r15) t := by
  have pcT : t.pc = Add.entry+0x120 := by
    have h := walked.pc
    simpa using h
  obtain ⟨cacheLoad,_,_⟩ := trunk.cacheAt
  have run : Eventually (instructionStep fetch) (fun e => ∃ u, Held c a u ∧
      e.data.regs = {u.regs with rsi := 3520, rdi := .ofBitVec (BitVec.ofNat 64 L.cache), rsp := u.regs.rsp-8} ∧
      e.data.dmem = Placement.callMemory u 0x144 ∧ e.pc = allocEntry ∧
      u.regs.rbx = t.data.regs.rbx ∧ u.regs.rbp = t.data.regs.rbp ∧
      u.regs.r14 = t.data.regs.r14 ∧ u.regs.r15 = t.data.regs.r15) ⟨t.data,Add.entry+0x120⟩ := by
    apply eventually_trans (instructionStep fetch) _ _ _
      (walked.held.call fetch premises.tracePc (Add.entry+0x120) (premises.insertion.add _ _ (by rfl)))
    rintro t1 ⟨pc1,held1,bx1,bp1,r14_1,r15_1⟩
    have pc1' : t1.pc = Add.entry+0x125 := pc1
    rw [Placement.at_pc t1 _ pc1']
    obtain ⟨old1,mapped1⟩ := Option.isSome_iff_exists.mp held1.ready.mapped
    have called := region_callback fetch (.ofNat 0xffffffff810f40c0) (Add.entry+0x12e) .constCmp1
      premises.callbacks.constCmp1 c ⟨t1.data,Add.entry+0x125⟩ t1.data
      {t1.data.regs with rsi := 0, rdi := 0} held1.ready
      (region_eventually (Add_r125_layout.agreement premises.insertion.add) t1.data _
        (const_arguments t1.data old1 mapped1))
    apply eventually_trans (instructionStep fetch) _ _ _ called
    rintro t2 ⟨pc2,sp2,bx2,bp2,r12_2,r13_2,r14_2,r15_2,ready2,frame2⟩
    have held2 := held1.next ready2 sp2 r12_2 r13_2 frame2
    rw [Placement.at_pc t2 _ pc2]
    apply eventually_trans (instructionStep fetch) _ _ _
      (held2.call fetch premises.tracePc (Add.entry+0x12e) (premises.insertion.add _ _ (by rfl)))
    rintro t3 ⟨pc3,held3,bx3,bp3,r14_3,r15_3⟩
    have pc3' : t3.pc = Add.entry+0x133 := pc3
    rw [Placement.at_pc t3 _ pc3']
    obtain ⟨old3,mapped3⟩ := Option.isSome_iff_exists.mp held3.ready.mapped
    have global3 : t3.data.dmem.loadInt nodeCacheAddress 8 = some ((BitVec.ofNat 64 L.cache).toNat : Int) := by
      rw [held3.outside_load _ 8 trunk.cacheWide]
      exact cacheLoad
    apply eventually_weaken (instructionStep fetch) _ _ _ _
      (region_eventually (Add_r133_layout.agreement premises.insertion.add) t3.data _
        (node_alloc_arguments t3.data old3 (BitVec.ofNat 64 L.cache) global3 mapped3))
    rintro e ⟨regsE,memE,pcE⟩
    exact ⟨t3.data,held3,regsE,memE,pcE,bx3.trans (bx2.trans bx1),bp3.trans (bp2.trans bp1),
      r14_3.trans (r14_2.trans r14_1),r15_3.trans (r15_2.trans r15_1)⟩
  have run' := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch run)
  rw [Placement.at_pc t _ pcT]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run'
  rintro e ⟨⟨⟨u,held,regs,mem,pc,bx,bp,r14,r15⟩,mapped⟩,_,forward⟩
  exact ⟨u,⟨held,regs,mem,pc,fun x n h => mapped x n (walked.mapped x n h),forward.trans walked.forward⟩,
    bx,bp,r14,r15⟩

/-- A state of `add`'s frame after the service at :205 returned, with the
word `word` in `(%rsp)`. -/
structure Mid (L : Statements.C1.Layout) (A : Allocator) (c : Context) (s : MachineState) (v4 : Bool)
    (names : Allowedips.Names) (d : Device) (seq : BitVec 64) (a : MachineData) (bits : Nat)
    (placed : Option NodeId) (word : UInt64) (m : MachineData) : Prop where
  ready : CallsReady c m
  stack : m.regs.rsp = a.regs.rsp - 96
  rbx : m.regs.rbx = Placement.ptr (Trie.interpretation names.trie.nodes) placed
  rbp : m.regs.rbp.toNat = bits
  r12 : m.regs.r12 = .ofBitVec ((a.regs.get (.low .rcx .W32)).setWidth 64)
  r13 : m.regs.r13 = a.regs.rdx
  r14 : m.regs.r14 = a.regs.r8
  r15 : m.regs.r15.toNat = bits
  base : m.dmem.loadInt m.regs.rsp.toBitVec 8 = some (word.toNat : Int)
  loads : ∀ off n : Nat, 16 ≤ off → off+n ≤ 112 → (off+n ≤ 32 ∨ (40 ≤ off ∧ off+n ≤ 44) ∨ 48 ≤ off) →
    m.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n =
      (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n
  frame : EqualOutside (fun x =>
    InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
      (insertWindow + A.depth - frameSize v4 + 8) x ∨ c.writes x ∨ L.Heap x) a.dmem m.dmem
  related : Allowedips.Corresponds names Root.nodeOffsets m.dmem (bump d)
  shape : Allowedips.heap names (Allowedips.target (bump d)) m.dmem = .ok ()
  seqWord : m.dmem.loadInt (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 =
    some ((1+seq).toNat : Int)
  mapped : MappedLe s.data.dmem m.dmem
  forward : m.system.bits[10] = false

theorem seq_in_heap (L : Statements.C1.Layout) (i : Nat) (hi : i < 8) :
    L.Heap (BitVec.ofNat 64 (L.table+AllowedipsMutationLayout.seq) + .ofNat 64 i) :=
  ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.heap, Layout.fixed, tableFields],⟨i,hi,rfl⟩⟩

variable {bits : Nat} {placed : Option NodeId} {word : UInt64} {m : MachineData}

theorem Mid.stackAt (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (mid : Mid L A c s v4 names d seq a bits placed word m) :
    m.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 96) := by
  rw [mid.stack]
  show a.regs.rsp.toBitVec - BitVec.ofNat 64 96 = _
  rw [trunk.atAdd.stackAt, sub_sub_ofNat]

/-- The call is in flight at a state after the service. -/
theorem Mid.flight (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (mid : Mid L A c s v4 names d seq a bits placed word m) (pc : Int64) :
    InFlight L A c s ⟨m,pc⟩ := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have value : m.regs.rsp.toNat = s.data.regs.rsp.toNat - (frameSize v4 + 96) := by
    show m.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toBitVec.toNat - _
    rw [mid.stackAt trunk]
    exact toNat_sub_ofNat _ _ (by omega)
  refine ⟨by show s.data.regs.rsp.toNat ≤ m.regs.rsp.toNat + insertWindow; rw [value]; unfold insertWindow; omega,
    by show m.regs.rsp.toNat ≤ s.data.regs.rsp.toNat; rw [value]; omega,?_,mid.mapped,mid.forward,
    mid.ready.state⟩
  intro x hx
  refine (trunk.atAdd.frameAt x (fun h => hx ?_)).trans (mid.frame x (fun h => hx ?_))
  · rcases h with h | h | h
    · exact .inl (below_sub _ _ _ _ _ (by omega) (by omega) x h)
    · exact .inr (.inr (seq_heap _ trunk.tableReg x h))
    · exact .inr (.inl h)
  · rcases h with h | h | h
    · exact .inl (range_mono _ _ _ (by omega) x h)
    · exact .inr (.inl h)
    · exact .inr (.inr h)

/-- A coverage call after the service: everything is kept, the heap unchanged. -/
theorem Mid.call (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (mid : Mid L A c s v4 names d seq a bits placed word m) (pc : Int64)
    (here : fetch pc = some ⟨callInstruction "L_ffffffff810f31f0",5⟩) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc = pc+5 ∧ Mid L A c s v4 names d seq a bits placed word t.data ∧
      ∀ y, L.Heap y → t.data.dmem.get? y = m.dmem.get? y) ⟨m,pc⟩ := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have r := trunk.resources
  have run := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch
    (Services.call fetch pc "L_ffffffff810f31f0" .pc premises.tracePc here c m mid.ready))
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨⟨⟨pcT,sp,bx,bp,r12,r13,r14,r15,ready,frame⟩,mapped⟩,_,forward⟩
  rw [call_word a m mid.stack] at frame
  have notCall (y : BitVec 64) (hy : L.Heap y) :
      ¬(InRange (a.regs.rsp.toBitVec-104) 8 y ∨ c.writes y) := fun h =>
    h.elim (fun p => (trunk.heapWide y hy).1 (wide_sub a 0 8 (by decide) y (by simpa using p)))
      (trunk.heapWide y hy).2
  have readApart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ y, span.contains y →
      ¬(InRange (a.regs.rsp.toBitVec-104) 8 y ∨ c.writes y) := fun span member y inside =>
    notCall y (read_heap trunk.table trunk.peers trunk.inArena span member y inside)
  have windowLoad (off n : Nat) (lo : 8 ≤ off) (hi : off+n ≤ 112) :
      t.data.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n =
        m.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n := by
    refine (frame.loadInt _ n (fun i hi' h => ?_)).symm
    rcases h with p | cw
    · exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) off n 0 8 (by omega) (by omega)
        (.inr (by omega)) _ ⟨i,hi',rfl⟩ (by simpa using p)
    · exact r.coverageApart _ (writes_bytes cw) (window_sub a off n hi _ ⟨i,hi',rfl⟩)
  have spZero : m.regs.rsp.toBitVec = a.regs.rsp.toBitVec-104+.ofNat 64 8 := by
    have h := sp_frame a m.regs.rsp mid.stack 0
    simpa using h
  refine ⟨pcT,⟨ready,sp.trans mid.stack,bx.trans mid.rbx,by rw [bp]; exact mid.rbp,r12.trans mid.r12,
    r13.trans mid.r13,r14.trans mid.r14,by rw [r15]; exact mid.r15,?_,?_,?_,
    (reconstruct_frame names Root.nodeOffsets frame readApart).symm.trans mid.related,
    (heap_frame names Root.nodeOffsets _ frame
      (fun span member => readApart span (metadata_read member))).symm.trans mid.shape,?_,
    fun x n h => mapped x n (mid.mapped x n h),forward.trans mid.forward⟩,
    fun y hy => (frame y (notCall y hy)).symm⟩
  · rw [sp, spZero, windowLoad 8 8 (by decide) (by decide), ← spZero]
    exact mid.base
  · intro off n lo hi clear
    rw [windowLoad off n (by omega) hi]
    exact mid.loads off n lo hi clear
  · intro y hy
    refine (mid.frame y hy).trans (frame y (fun h => hy ?_))
    rcases h with h | h
    · exact .inl (wide_tight trunk.atAdd _ wide y (wide_sub a 0 8 (by decide) y (by simpa using h)))
    · exact .inr (.inl h)
  · rw [← frame.loadInt _ 8 (fun i hi' h => notCall _ (seq_in_heap L i hi') h)]
    exact mid.seqWord

/-- The service call at :205 and the store of its result at +0x144. -/
theorem node_called (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (at' : AtCall L c a u e 0x144)
    (bx : u.regs.rbx = Placement.ptr (Trie.interpretation names.trie.nodes) placed)
    (bp : u.regs.rbp.toNat = bits) (r14 : u.regs.r14 = a.regs.r8) (r15 : u.regs.r15.toNat = bits)
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 78) :
    Eventually (instructionStep fetch) (fun b => ∃ t1 : MachineState,
      AllocResult L A (names.trie.nodes.map (·.2)) record rest t1 ∧
      Mid L A c s v4 names d seq a bits placed t1.data.regs.rax b.data ∧
      b.pc = (if t1.data.regs.rax.toBitVec = 0 then Add.entry+0x692 else Add.entry+0x151) ∧
      b.data.regs.rax = t1.data.regs.rax ∧
      ∀ y, L.Heap y → b.data.dmem.get? y = t1.data.dmem.get? y) e := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have r := trunk.resources
  have tight := wide_tight trunk.atAdd (insertWindow + A.depth) wide
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have flightE := at'.flight trunk
  have stackE := at'.stackAt trunk
  have idleE : A.Idle e.data.dmem (names.trie.nodes.map (·.2)) (record :: rest) :=
    pending ▸ at'.idle premises trunk
  have recorded : ((Add.entry+.ofNat 0x144).toUInt64.toNat, record.site) ∈ allocSites := by
    rw [recordSite]
    decide
  apply eventually_trans (instructionStep fetch) _ _ _
    (at'.call alloc premises ready trunk _ trunk.liveArena record rest _ rfl recorded idleE)
  rintro t1 ⟨returned,result,flightT,kept⟩
  obtain ⟨pc1,sp1,bx1,bp1,r12_1,r13_1,r14_1,r15_1⟩ := returned
  have sp1' : t1.data.regs.rsp = u.regs.rsp := by
    rw [sp1, at'.regs]
    exact UInt64.sub_add_cancel _ _
  have pc1' : t1.pc = Add.entry+0x144 := pc1
  have stack1 : t1.data.regs.rsp = a.regs.rsp - 96 := sp1'.trans at'.held.stack
  have t1BV : t1.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 96) := by
    rw [stack1]
    show a.regs.rsp.toBitVec - BitVec.ofNat 64 96 = _
    rw [trunk.atAdd.stackAt, sub_sub_ofNat]
  have mapped1 : (t1.data.dmem.loadInt t1.data.regs.rsp.toBitVec 8).isSome = true := by
    rw [t1BV]
    exact flightT.mapped _ _ (trunk.caller.below.load _ 8 (by omega) (by omega))
  obtain ⟨old,mappedOld⟩ := Option.isSome_iff_exists.mp mapped1
  rw [Placement.at_pc t1 _ pc1']
  have run := SystemInvariant.eventually_mode fetch
    (region_eventually (Add_r144_layout.agreement premises.insertion.add) t1.data _
      (node_alloc_result t1.data old mappedOld))
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro b ⟨⟨regsB,memB,pcB⟩,_,forwardB⟩
  have spB : b.data.regs.rsp = u.regs.rsp := by rw [regsB]; exact sp1'
  have stored := storeInt_frame t1.data.dmem t1.data.regs.rsp.toBitVec 8 t1.data.regs.rax.toBitVec.toInt
  have inParent (y : BitVec 64) (h : InRange t1.data.regs.rsp.toBitVec 8 y) : Locals a y :=
    locals_parent a _ stack1 y h
  have heapNotParent (y : BitVec 64) (hy : L.Heap y) : ¬InRange t1.data.regs.rsp.toBitVec 8 y :=
    fun h => (trunk.heapWide y hy).1 (wide_of_locals a y (inParent y h))
  have word := call_word a u at'.held.stack
  have valueE : s.data.regs.rsp.toNat + 8 - e.data.regs.rsp.toNat = frameSize v4 + 104 + 8 := by
    show s.data.regs.rsp.toBitVec.toNat + 8 - e.data.regs.rsp.toBitVec.toNat = _
    rw [stackE, toNat_sub_ofNat _ _ (by omega)]
    omega
  have wordE : e.data.regs.rsp.toBitVec = a.regs.rsp.toBitVec - 104 := by
    rw [at'.regs]
    exact word
  have keptFrame : EqualOutside (fun y => ¬Protected L s e (names.trie.nodes.map (·.2)) y)
      e.data.dmem t1.data.dmem := fun y hy => (kept y (Classical.not_not.mp hy)).symm
  obtain ⟨relatedE,shapeE⟩ := at'.related trunk
  obtain ⟨relatedT,shapeT⟩ := protected_related trunk.table trunk.peers kept relatedE shapeE
  have readApart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ y, span.contains y →
      ¬InRange t1.data.regs.rsp.toBitVec 8 y := fun span member y inside =>
    heapNotParent y (read_heap trunk.table trunk.peers trunk.inArena span member y inside)
  refine ⟨t1,result,⟨?_,spB.trans at'.held.stack,by rw [regsB, bx1, at'.regs]; exact bx,
    by rw [regsB, bp1, at'.regs]; exact bp,by rw [regsB, r12_1, at'.regs]; exact at'.held.cidr12,
    by rw [regsB, r13_1, at'.regs]; exact at'.held.key,by rw [regsB, r14_1, at'.regs]; exact r14,
    by rw [regsB, r15_1, at'.regs]; exact r15,?_,?_,?_,?_,?_,?_,?_,forwardB.trans flightT.forward⟩,
    pcB,by rw [regsB],fun y hy => by rw [memB]; exact (stored y (heapNotParent y hy)).symm⟩
  · refine ⟨?_,by rw [spB]; exact at'.held.ready.aligned,?_,
      by rw [spB]; exact at'.held.ready.pushSeparate,by rw [spB]; exact at'.held.ready.returnSeparate,
      at'.held.ready.metadataSeparate,at'.held.ready.preemptSeparate⟩
    · rw [memB]
      exact state_frame c t1.data.dmem _ flightT.coverage _ stored
        (fun y read h => trunk.bytesWide y read (wide_of_locals a y (inParent y h)))
    · rw [memB, spB]
      apply storeInt_defined
      apply flightT.mapped
      have at'' : u.regs.rsp.toBitVec - 8 = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104) := by
        rw [← stackE, at'.regs]
        rfl
      rw [at'']
      exact trunk.caller.below.load _ 8 (by omega) (by omega)
  · rw [memB, regsB]
    exact load64_store _ _ _
  · intro off n lo hi clear
    rw [memB, load_store_apart _ _ _ _ _ _ (fun y hy hs => not_locals a off n lo hi clear y hy (inParent y hs)),
      ← keptFrame.loadInt _ n (fun i hi' h => h (.inl (by
        rw [wordE, valueE]
        exact ⟨off+i,by omega,by rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩))), at'.mem]
    have skip := (storeInt_frame u.dmem (u.regs.rsp.toBitVec-8) 8
      (Add.entry+.ofNat 0x144).toBitVec.toInt).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n
      (fun i hi' h => by
        rw [word] at h
        exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) off n 0 8 (by omega) (by omega)
          (.inr (by omega)) _ ⟨i,hi',rfl⟩ (by simpa using h))
    exact skip.symm.trans (at'.held.window_load r off n lo hi clear)
  · intro y hy
    have service := alloc_frame trunk (frameSize v4 + 104) (by omega) stackE flightE flightT kept
    refine (at'.fromAdd y (fun h => hy ?_)).trans ((service y (fun h => hy ?_)).trans ?_)
    · rcases h with h | h
      · exact .inl (tight y h)
      · exact .inr (.inl h)
    · rcases h with h | h | h
      · exact .inl (range_mono _ _ _ (by omega) y h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rw [memB]
      exact stored y (fun h => hy (.inl (tight y (wide_of_locals a y (inParent y h)))))
  · rw [memB]
    exact (reconstruct_frame names Root.nodeOffsets stored readApart).symm.trans relatedT
  · rw [memB]
    exact (heap_frame names Root.nodeOffsets _ stored
      (fun span member => readApart span (metadata_read member))).symm.trans shapeT
  · rw [memB, ← stored.loadInt _ 8 (fun i hi' h => heapNotParent _ (seq_in_heap L i hi') h),
      ← keptFrame.loadInt _ 8 (fun i hi' h => h (.inr (.inl
        ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.fixed, tableFields],⟨i,hi',rfl⟩⟩))),
      ← at'.fromAdd.loadInt _ 8 (fun i hi' h =>
        h.elim (trunk.heapWide _ (seq_in_heap L i hi')).1 (trunk.heapWide _ (seq_in_heap L i hi')).2),
      ← seq_address _ L.table trunk.tableReg]
    exact trunk.atAdd.seqWord
  · intro x n h
    rw [memB]
    exact storeInt_defined _ _ _ _ _ _ (flightT.mapped x n h)
end

#print axioms node_reach
#print axioms Mid.call
#print axioms node_called
end C1Trunk
