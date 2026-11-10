import C1TrunkFresh
import AllowedipsRootChecked
/-! Result C1, package 2: the empty root with the node installed. From
`add`'s entry through the allocation to the landed boundary `Root.boundary`
at +0x443, derived from `Trunk` and `AllocRule` (after trial T4's
`boundary_established`, whose three helper lemmas are copied). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem frame_address (s0 : MachineData) (k : Nat) :
    BitVec.ofNat 64 ((s0.regs.rsp-96).toNat+k) = s0.regs.rsp.toBitVec-104+.ofNat 64 (8+k) := by
  rw [BitVec.ofNat_add, Root.ofNat_uint64, UInt64.toBitVec_sub, BitVec.ofNat_add, ← BitVec.add_assoc]
  congr 1
  show s0.regs.rsp.toBitVec-96#64 = s0.regs.rsp.toBitVec-104#64+8#64
  bv_omega

/-- The converse of the landed `Root.boundary_fields`. -/
theorem boundary_of_fields {names o world machine key cidr pid}
    (f : Root.BoundaryFields names o world machine key cidr pid) :
    Root.boundary names o world machine key cidr pid = .ok () := by
  obtain ⟨d,device,empty⟩ := f.device
  have family : (machine.data.regs.rbp.toNat==32 || machine.data.regs.rbp.toNat==128) = true := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using f.family
  unfold Root.boundary
  simp [f.asserted,device,f.pc,f.owner,f.cidrRead,f.allocated,f.zero,f.query,f.saved,f.apart,
    family,empty,f.cidrBound,require,bind,Except.bind,Except.mapError]

theorem readNat_frame {before after : MachineState} {writes : BitVec 64 → Prop}
    (frame : EqualOutside writes before.data.dmem after.data.dmem) (a n : Nat)
    (apart : ∀ x, InRange (.ofNat 64 a) n x → ¬writes x) :
    readNat before a n = readNat after a n := by
  have same := frame.loadBytes (.ofNat 64 a) n (fun i hi => apart _ ⟨i,hi,rfl⟩)
  simp only [readNat,same]

/-- The state at +0x443 on the empty-root path, with what the rest of the
path needs besides the landed boundary. -/
structure AtBoundary (L : Statements.C1.Layout) (A : Allocator) (c : Context) (s : MachineState)
    (v4 : Bool) (names : Allowedips.Names) (rest : List HiddenRecord) (d : Device) (seq : BitVec 64)
    (a : MachineData) (n : Nat) (v : MachineState) : Prop where
  pc : v.pc = Add.entry+0x443
  object : Object L names n
  rbx : v.data.regs.rbx.toNat = n
  bits : v.data.regs.rbp.toNat = if v4 then 32 else 128
  ready : CallsReady c v.data
  stack : v.data.regs.rsp = a.regs.rsp - 96
  loads : ∀ off m : Nat, 8 ≤ off → off+m ≤ 112 →
    v.data.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) m =
      (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) m
  idle : A.Idle v.data.dmem (names.trie.nodes.map (·.2) ++ [n]) rest
  frame : EqualOutside (fun x =>
    InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
      (insertWindow + A.depth - frameSize v4 + 8) x ∨ c.writes x ∨ L.Heap x) a.dmem v.data.dmem
  seqWord : v.data.dmem.loadInt (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 =
    some ((1+seq).toNat : Int)
  related : Allowedips.Corresponds names Root.nodeOffsets v.data.dmem (bump d)
  shape : Allowedips.heap names (Allowedips.target (bump d)) v.data.dmem = .ok ()
  zero : readNat v n 72 = .ok 0
  r13 : v.data.regs.r13 = a.regs.rdx
  r14 : v.data.regs.r14 = a.regs.r8

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- Empty root, the service hands out an object: `add`'s entry to +0x443. -/
theorem root_allocated (below : NodeBelowTop) (alloc : AllocRule) (premises : Premises fetch L A)
    {family : Nat} (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128))
    (empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none)
    (record : HiddenRecord) (rest : List HiddenRecord) (pending : stream = record :: rest)
    (recordSite : record.site = 77) (ok : record.bytes.head? = some 1) :
    Eventually (instructionStep fetch) (fun v => ∃ n, AtBoundary L A c s v4 names rest d seq a n v)
      ⟨a,Add.entry⟩ := by
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
  obtain ⟨pc1,sp1,_,bp1,_,r13_1,r14_1,_⟩ := returned
  obtain ⟨object,zero1,idle1⟩ := object_of_result below premises trunk result ok
  have nonNull : t1.data.regs.rax.toBitVec ≠ 0 := by
    intro h
    have zero : t1.data.regs.rax.toNat = 0 := by
      show t1.data.regs.rax.toBitVec.toNat = 0
      rw [h]
      rfl
    have positive := object.positive
    omega
  have sp1' : t1.data.regs.rsp = u.regs.rsp := by
    rw [sp1, at'.regs]
    exact UInt64.sub_add_cancel _ _
  have pc1' : t1.pc = Add.entry+0x432 := pc1
  rw [Placement.at_pc t1 _ pc1']
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r432_layout.agreement premises.insertion.add) t1.data _ (alloc_result t1.data))
  rintro b ⟨regsB,memB,pcB⟩
  rw [ite_eq_right nonNull] at pcB
  have spBU : b.data.regs.rsp = u.regs.rsp := by rw [regsB]; exact sp1'
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
  have readyB : CallsReady c b.data := by
    refine ⟨memB ▸ flightT.coverage,by rw [spBU]; exact at'.live.ready.aligned,?_,
      by rw [spBU]; exact at'.live.ready.pushSeparate,by rw [spBU]; exact at'.live.ready.returnSeparate,
      at'.live.ready.metadataSeparate,at'.live.ready.preemptSeparate⟩
    rw [memB, spBU]
    apply flightT.mapped
    have at'' : u.regs.rsp.toBitVec - 8 = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104) := by
      rw [← stackE, at'.regs]
      rfl
    rw [at'']
    exact trunk.caller.below.load _ 8 (by omega) (by omega)
  rw [Placement.at_pc b _ pcB]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Services.call fetch (Add.entry+0x43e) "L_ffffffff810f31f0" .pc premises.tracePc
      (premises.insertion.add _ _ (by rfl)) c b.data readyB)
  rintro v ⟨pcV,spV,bxV,bpV,_,r13V,r14V,_,readyV,frameV⟩
  rw [memB, spBU, word] at frameV
  have heapOut := trunk.heapOutside
  have notCall (y : BitVec 64) (hy : L.Heap y) :
      ¬(InRange (a.regs.rsp.toBitVec-104) 8 y ∨ c.writes y) := fun h =>
    h.elim (fun p => (heapOut y hy).1 (window_sub a 0 8 (by decide) y (by simpa using p))) (heapOut y hy).2
  obtain ⟨relatedE,shapeE⟩ := at'.related trunk
  obtain ⟨relatedT,shapeT⟩ := protected_related trunk.table trunk.peers kept relatedE shapeE
  have readApart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ y, span.contains y →
      ¬(InRange (a.regs.rsp.toBitVec-104) 8 y ∨ c.writes y) := fun span member y inside =>
    notCall y (read_heap trunk.table trunk.peers trunk.inArena span member y inside)
  have seqHeap (i : Nat) (hi' : i < 8) :
      L.Heap (BitVec.ofNat 64 (L.table+AllowedipsMutationLayout.seq) + .ofNat 64 i) :=
    ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.heap, Layout.fixed, tableFields],⟨i,hi',rfl⟩⟩
  have nodeHeap (y : BitVec 64) (inside : InRange (.ofNat 64 t1.data.regs.rax.toNat) 72 y) : L.Heap y := by
    obtain ⟨home,isArena,low,high⟩ := object.arena
    exact arena_heap y ⟨home,isArena,span_within _ _ _ _ low (by unfold nodeSize at high; omega) y inside⟩
  refine ⟨t1.data.regs.rax.toNat,pcV,object,by rw [bxV, regsB],?_,readyV,
    (spV.trans spBU).trans at'.live.stack,?_,?_,?_,?_,
    (reconstruct_frame names Root.nodeOffsets frameV readApart).symm.trans relatedT,
    (heap_frame names Root.nodeOffsets _ frameV
      (fun span member => readApart span (metadata_read member))).symm.trans shapeT,?_,
    r13V.trans (by rw [regsB]; exact r13_1.trans (by rw [at'.regs]; exact at'.live.key)),
    r14V.trans (by rw [regsB]; exact r14_1.trans (by rw [at'.regs]; exact at'.live.peer))⟩
  · rw [bpV, regsB]
    show t1.data.regs.rbp.toNat = _
    rw [bp1, at'.regs]
    show u.regs.rbp.toNat = _
    rw [at'.live.bits]
    show (BitVec.setWidth 64 (a.regs.get (.low .rsi .W32))).toNat = _
    have lt : (a.regs.get (.low .rsi .W32)).toNat < 2^32 := (a.regs.get (.low .rsi .W32)).isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    exact trunk.atAdd.bits
  · intro off m lo hi
    rw [← frameV.loadInt _ m (fun i hi' h => by
      rcases h with p | cw
      · exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) off m 0 8 (by omega) (by omega)
          (.inr (by omega)) _ ⟨i,hi',rfl⟩ (by simpa using p)
      · exact r.coverageApart _ (writes_bytes cw) (window_sub a off m hi _ ⟨i,hi',rfl⟩)),
      ← keptFrame.loadInt _ m (fun i hi' h => h (.inl (by
        rw [wordE, valueE]
        exact ⟨off+i,by omega,by rw [BitVec.add_assoc, ← BitVec.ofNat_add]⟩))), at'.mem]
    have skip := (storeInt_frame u.dmem (u.regs.rsp.toBitVec-8) 8
      (Add.entry+.ofNat 0x432).toBitVec.toInt).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) m
      (fun i hi' h => by
        rw [word] at h
        exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) off m 0 8 (by omega) (by omega)
          (.inr (by omega)) _ ⟨i,hi',rfl⟩ (by simpa using h))
    exact skip.symm.trans (at'.live.window_load r off m lo hi)
  · exact premises.allocator.frame t1.data.dmem v.data.dmem _ _ idle1
      (fun y arena _ => frameV y (notCall y (arena_heap y arena)))
  · intro y hy
    have service := alloc_frame trunk (frameSize v4 + 104) (by omega) stackE flightE flightT kept
    refine (at'.fromAdd y (fun h => hy ?_)).trans ((service y (fun h => hy ?_)).trans
      (frameV y (fun h => hy ?_)))
    · rcases h with h | h
      · exact .inl (tight y h)
      · exact .inr (.inl h)
    · rcases h with h | h | h
      · exact .inl (range_mono _ _ _ (by omega) y h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rcases h with h | h
      · exact .inl (tight y (window_sub a 0 8 (by decide) y (by simpa using h)))
      · exact .inr (.inl h)
  · rw [← frameV.loadInt _ 8 (fun i hi' h => notCall _ (seqHeap i hi') h),
      ← keptFrame.loadInt _ 8 (fun i hi' h => h (.inr (.inl
        ⟨(L.table+AllowedipsMutationLayout.seq,8),by simp [Layout.fixed, tableFields],⟨i,hi',rfl⟩⟩))),
      ← at'.fromAdd.loadInt _ 8 (fun i hi' h =>
        h.elim (heapOut _ (seqHeap i hi')).1 (heapOut _ (seqHeap i hi')).2),
      ← seq_address _ L.table trunk.tableReg]
    exact trunk.atAdd.seqWord
  · rw [← readNat_frame (before := t1) (after := v) frameV _ 72 (fun y inside => notCall y (nodeHeap y inside))]
    exact zero1

/-- The landed boundary of the root initialization holds at +0x443. -/
theorem root_boundary (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128))
    (empty : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none)
    {rest : List HiddenRecord} {n : Nat} {v : MachineState}
    (at' : AtBoundary L A c s v4 names rest d seq a n v) :
    Root.boundary names Root.nodeOffsets (bumped w d) v key cidr pid = .ok () := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room := trunk.sep.room
  have top := trunk.sep.top
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := room
  have top' : s.data.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 := top
  have stackAt := trunk.atAdd.stackAt
  have vspBV : v.data.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 96) := by
    rw [at'.stack]
    show a.regs.rsp.toBitVec - BitVec.ofNat 64 96 = _
    rw [stackAt, sub_sub_ofNat]
  have vspNat : v.data.regs.rsp.toNat = s.data.regs.rsp.toBitVec.toNat - (frameSize v4 + 96) := by
    show v.data.regs.rsp.toBitVec.toNat = _
    rw [vspBV, toNat_sub_ofNat _ _ (by omega)]
  have nq : 0 < (if v4 then 32 else 128)/8 ∧ (if v4 then 32 else 128)/8 ≤ (if v4 then 36 else 48) := by
    cases v4 <;> decide
  have kq : 36 ≤ (if v4 then 36 else 48) ∧ (if v4 then 36 else 48) + 8 ≤ frameSize v4 := by
    cases v4 <;> decide
  have r13BV : v.data.regs.r13.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (if v4 then 36 else 48) := by
    rw [at'.r13, trunk.atAdd.query]
    cases v4 <;> rfl
  have r13Nat : v.data.regs.r13.toNat = s.data.regs.rsp.toBitVec.toNat - (if v4 then 36 else 48) := by
    show v.data.regs.r13.toBitVec.toNat = _
    rw [r13BV, toNat_sub_ofNat _ _ (by omega)]
  have aboveLoad (k m : Nat) (hk : k + 8 ≤ frameSize v4) (hm : m ≤ k) :
      v.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) m =
        a.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) m := by
    refine (at'.frame.loadInt _ m (fun i hi h => ?_)).symm
    have inWindow : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
        (insertWindow + A.depth + 8) (s.data.regs.rsp.toBitVec - .ofNat 64 k + .ofNat 64 i) :=
      below_sub _ k m _ _ (by omega) (by omega) _ ⟨i,hi,rfl⟩
    rcases h with h | h | h
    · exact below_under _ k m (insertWindow + A.depth) _ (by omega) (by omega) (by omega) _ ⟨i,hi,rfl⟩ h
    · exact trunk.sep.bytesStack _ (writes_bytes h) inWindow
    · exact trunk.sep.heapStack _ h inWindow
  have argCidr : (a.regs.get (.low .rcx .W32)).toNat = cidr := trunk.atAdd.cidr.trans trunk.cidr
  have tableTop := (Root.table_valid_geometry (related_valid trunk.relatedA)).1
  have argSlot : a.regs.rdi.toNat = names.table+(if (if v4 then 32 else 128) = 32 then 0 else 8) := by
    have h := congrArg BitVec.toNat trunk.slotAt
    have small : (if (if v4 then 32 else 128) = 32 then 0 else 8) ≤ 8 := by
      repeat' split
      all_goals omega
    have lt : names.table+(if (if v4 then 32 else 128) = 32 then 0 else 8) < 2^64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt] at h
    exact h
  apply boundary_of_fields
  refine {
    asserted := assertAt_of_related rfl at'.related at'.shape
    device := ⟨bump d,rfl,?_⟩
    pc := at'.pc
    family := by rw [at'.bits]; cases v4 <;> simp
    owner := by rw [at'.r14, trunk.atAdd.peer, trunk.peers]; exact trunk.peer
    cidrRead := ?_
    cidrBound := by rw [at'.bits]; exact bound
    allocated := by rw [at'.rbx]; exact at'.object.valid
    zero := by rw [at'.rbx]; exact at'.zero
    query := ?_
    saved := ?_
    apart := ?_ }
  · rw [at'.bits]
    cases v4 <;> simpa [bump] using empty
  · apply readNat_of_load
    show v.data.dmem.loadInt (.ofNat 64 (v.data.regs.rsp.toNat+16)) 4 = some (cidr : Int)
    rw [at'.stack, frame_address, at'.loads (8+16) 4 (by decide) (by decide)]
    have read := memory_cidr a
    rw [slot_base a 7 (by decide)] at read
    have same : a.regs.get (.low .rcx .W32) = BitVec.extractLsb' 0 32 a.regs.rcx.toBitVec := by
      simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
    rw [← argCidr, same]
    exact read
  · rw [at'.bits]
    have keyWord := trunk.atAdd.keyWord
    cases v4
    · simp only [Bool.false_eq_true, ↓reduceIte] at keyWord r13BV
      have rdHigh : readNat v v.data.regs.r13.toNat 8 = .ok (key/2^64) := by
        apply readNat_of_load
        rw [Root.ofNat_uint64, r13BV, aboveLoad 48 8 (by decide) (by decide)]
        exact keyWord.1
      have rdLow : readNat v (v.data.regs.r13.toNat+8) 8 = .ok (key % 2^64) := by
        apply readNat_of_load
        rw [BitVec.ofNat_add, Root.ofNat_uint64, r13BV, sub_add_ofNat _ 48 8 (by omega),
          show (48-8 : Nat) = 40 from rfl, aboveLoad 40 8 (by decide) (by decide)]
        exact keyWord.2
      simp [Placement.queryLocals, Placement.query6, rdHigh, rdLow, require, bind, Except.bind,
        Nat.div_add_mod']
    · simp only [↓reduceIte] at keyWord r13BV
      have rd : readNat v v.data.regs.r13.toNat 4 = .ok key := by
        apply readNat_of_load
        rw [Root.ofNat_uint64, r13BV, aboveLoad 36 4 (by decide) (by decide)]
        exact keyWord
      simp [Placement.queryLocals, Placement.query4, rd, require, bind, Except.bind]
  · apply readNat_of_load
    show v.data.dmem.loadInt (.ofNat 64 (v.data.regs.rsp.toNat+8)) 8 = some _
    rw [at'.stack, frame_address, at'.loads (8+8) 8 (by decide) (by decide)]
    have read := memory_read a 8 6 (by decide) (by decide) (by decide)
    rw [slot_base a 6 (by decide)] at read
    rw [at'.bits, ← argSlot]
    exact read
  · rw [at'.rbx]
    apply apart_of_bytes
    · intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · rw [at'.bits]
        exact ⟨by show v.data.regs.r13.toNat + _ ≤ 2^64; rw [r13Nat]; omega,nq.1⟩
      · exact ⟨by show v.data.regs.rsp.toNat + 8 + 8 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
      · exact ⟨by show v.data.regs.rsp.toNat + 16 + 4 ≤ 2^64; rw [vspNat]; omega,Nat.zero_lt_succ _⟩
    · exact fun span member => (at'.object.writeSpans trunk v.data at'.rbx span member).1
    · intro stackSpan member heapSpan written x inside covered
      have inHeap := (at'.object.writeSpans trunk v.data at'.rbx heapSpan written).2 x covered
      apply trunk.sep.heapStack x inHeap
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · have inside' : InRange (.ofNat 64 v.data.regs.r13.toNat) (v.data.regs.rbp.toNat/8) x := inside
        rw [Root.ofNat_uint64, r13BV, at'.bits] at inside'
        exact below_sub _ _ _ _ _ (by omega) (by omega) x inside'
      · have inside' : InRange (.ofNat 64 (v.data.regs.rsp.toNat+8)) 8 x := inside
        rw [BitVec.ofNat_add, Root.ofNat_uint64, vspBV, sub_add_ofNat _ _ 8 (by omega)] at inside'
        exact below_sub _ _ _ _ _ (by omega) (by omega) x inside'
      · have inside' : InRange (.ofNat 64 (v.data.regs.rsp.toNat+16)) 4 x := inside
        rw [BitVec.ofNat_add, Root.ofNat_uint64, vspBV, sub_add_ofNat _ _ 16 (by omega)] at inside'
        exact below_sub _ _ _ _ _ (by omega) (by omega) x inside'
end

#print axioms root_allocated
#print axioms root_boundary
end C1Trunk
