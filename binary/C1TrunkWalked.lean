import C1TrunkHeader
import C1TrunkLoop
import C1TrunkSourceFacts
/-! Result C1, package 2: the walk on a nonempty root at the level of the
insertion: from `Trunk` (everything known at `add`'s entry) through the
header to the exit of the landed placement loop. `Walked` is the state at the
loop's exit (`+0x3ca` on an exact match, `+0x120` otherwise). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- A nonempty mirror root is the address of a named node in the root slot:
read off the reconstruction (after `root_word`). -/
theorem root_named {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    (related : Allowedips.Corresponds names o m d) (bits : Nat) (rootId : NodeId)
    (rootAt : (if bits = 32 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId) :
    ∃ base, (rootId,base) ∈ names.trie.nodes ∧ base ≠ 0 ∧
      m.loadInt (.ofNat 64 (names.table+(if bits = 32 then 0 else 8))) 8 = some (base : Int) := by
  have named (path : String) (raw : Nat) (h : Trie.pointer names.trie.nodes path raw = .ok (some rootId)) :
      (rootId,raw) ∈ names.trie.nodes ∧ raw ≠ 0 := by
    unfold Trie.pointer at h
    split at h
    · cases h
    · rename_i nonzero
      cases found : names.trie.nodes.find? (·.2 == raw) with
      | none => rw [found] at h; cases h
      | some pair =>
        rw [found] at h
        have equal : pair.1 = rootId := Option.some.inj (Except.ok.inj h)
        have second : pair.2 = raw := by
          have h' := List.find?_some found
          simpa using h'
        have member := List.mem_of_find?_eq_some found
        refine ⟨?_,fun zero => nonzero (by simp [zero])⟩
        rw [← equal, ← second]
        exact member
  unfold Allowedips.Corresponds Allowedips.reconstruct at related
  obtain ⟨_,_,h⟩ := bind_ok related
  obtain ⟨w4,hw4,h⟩ := bind_ok h
  obtain ⟨r4,hp4,h⟩ := bind_ok h
  obtain ⟨w6,hw6,h⟩ := bind_ok h
  obtain ⟨r6,hp6,h⟩ := bind_ok h
  obtain ⟨seq,_,h⟩ := bind_ok h
  obtain ⟨nodes,_,h⟩ := bind_ok h
  obtain ⟨peers,_,h⟩ := bind_ok h
  have eq := Except.ok.inj h
  have t4 : r4 = d.peerAllowedips.root4 := congrArg (·.table.root4) eq
  have t6 : r6 = d.peerAllowedips.root6 := congrArg (·.table.root6) eq
  by_cases four : bits = 32
  · simp only [four,↓reduceIte] at rootAt ⊢
    rw [t4,rootAt] at hp4
    exact ⟨w4,(named _ _ hp4).1,(named _ _ hp4).2,word_loadInt _ _ _ _ _ hw4⟩
  · simp only [four,↓reduceIte] at rootAt ⊢
    rw [t6,rootAt] at hp6
    exact ⟨w6,(named _ _ hp6).1,(named _ _ hp6).2,word_loadInt _ _ _ _ _ hw6⟩

section
variable {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator} {c : Context}
  {s : MachineState} {w : World} {v4 : Bool} {key cidr pid : Nat} {ra : UInt64}
  {names : Allowedips.Names} {stream : List HiddenRecord} {d : Device} {seq : BitVec 64}
  {a : MachineData}

/-- `add`'s frame with the helper's scratch lies in the insertion's window. -/
theorem wide_tight (atAdd : AtAdd c s.data seq v4 key a) (W : Nat) (wide : 200 ≤ W) (x : BitVec 64)
    (h : Wide a x) : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 W) (W - frameSize v4 + 8) x := by
  have fs := frameSize_range v4
  have h' : InRange (a.regs.rsp.toBitVec - .ofNat 64 144) 152 x := h
  rw [atAdd.stackAt, sub_sub_ofNat] at h'
  exact below_sub _ (frameSize v4 + 144) 152 W (W - frameSize v4 + 8) (by omega) (by omega) x h'

theorem Trunk.heapWide (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (x : BitVec 64) (h : L.Heap x) : ¬Wide a x ∧ ¬c.writes x := by
  have fs := frameSize_range v4
  refine ⟨fun hw => trunk.sep.heapStack x h (range_mono _ _ _ (by omega) x
    (wide_tight trunk.atAdd (insertWindow + A.depth) (window_wide A) x hw)),trunk.sep.heapWrites x h⟩

theorem Trunk.bytesWide (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (x : BitVec 64) (h : c.bytes x) : ¬Wide a x := by
  have fs := frameSize_range v4
  exact fun hw => trunk.sep.bytesStack x h (range_mono _ _ _ (by omega) x
    (wide_tight trunk.atAdd (insertWindow + A.depth) (window_wide A) x hw))

/-- The stack pointer of `add`'s frame against the insertion's. -/
theorem Held.stackAt (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {u : MachineData} (held : Held c a u) :
    u.regs.rsp.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 96) := by
  rw [held.stack]
  show a.regs.rsp.toBitVec - BitVec.ofNat 64 96 = _
  rw [trunk.atAdd.stackAt, sub_sub_ofNat]

/-- The relation at a held state. -/
theorem Held.related (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {u : MachineData} (held : Held c a u) :
    Allowedips.Corresponds names Root.nodeOffsets u.dmem (bump d) ∧
    Allowedips.heap names (Allowedips.target (bump d)) u.dmem = .ok () := by
  have apart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ x, span.contains x →
      ¬(Wide a x ∨ c.writes x) := by
    intro span member x inside h
    have out := trunk.heapWide x (read_heap trunk.table trunk.peers trunk.inArena span member x inside)
    exact h.elim out.1 out.2
  refine ⟨(reconstruct_frame names Root.nodeOffsets held.fromEntry apart).symm.trans trunk.relatedA,?_⟩
  exact (heap_frame names Root.nodeOffsets _ held.fromEntry
    (fun span member => apart span (metadata_read member))).symm.trans trunk.shapeA

/-- A read of the wrapper's frame (above `add`'s return word) at a held state. -/
theorem Held.above_load (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    {u : MachineData} (held : Held c a u) (k m : Nat) (hk : k + 8 ≤ frameSize v4) (hm : m ≤ k + 8) :
    u.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) m =
      a.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) m := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have top' : s.data.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 := trunk.sep.top
  apply held.outside_load
  intro x hx
  refine ⟨fun hw => ?_,fun hw => ?_⟩
  · exact below_under _ k m (insertWindow + A.depth) _ (by omega) (by omega) (by omega) x hx
      (wide_tight trunk.atAdd (insertWindow + A.depth) wide x hw)
  · exact trunk.sep.bytesStack x (writes_bytes hw)
      (below_sub _ k m (insertWindow + A.depth) (insertWindow + A.depth + 8) (by omega) (by omega) x hx)

/-- The loop's exit on a nonempty root. -/
structure Walked (c : Context) (names : Allowedips.Names) (d : Device) (a : MachineData) (bits : Nat)
    (placed : Option NodeId) (exact : Bool) (t : MachineState) : Prop where
  pc : t.pc = if exact then Add.entry+0x3ca else Add.entry+0x120
  held : Held c a t.data
  rbx : t.data.regs.rbx = Placement.ptr (Trie.interpretation names.trie.nodes) placed
  open' : exact = false → t.data.regs.rbp.toNat = bits ∧ t.data.regs.r14 = a.regs.r8
  r15 : t.data.regs.r15.toNat = bits
  owner : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+0x18) 8 = some (a.regs.r8.toNat : Int)
  related : Allowedips.Corresponds names Root.nodeOffsets t.data.dmem (bump d)
  shape : Allowedips.heap names (Allowedips.target (bump d)) t.data.dmem = .ok ()
  mapped : ∀ x n, (a.dmem.loadInt x n).isSome = true → (t.data.dmem.loadInt x n).isSome = true
  forward : t.data.system.bits[10] = a.system.bits[10]

/-- Nonempty root: `add`'s entry to the exit of the placement loop. -/
theorem trunk_walked (premises : Premises fetch L A)
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (bound : cidr ≤ (if v4 then 32 else 128)) (keyBound : key < 2^(if v4 then 32 else 128))
    (rootId : NodeId)
    (rootAt : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId)
    (rootNode : ∃ node, (bump d).nodes.get? rootId = some node ∧ node.bitlen = (if v4 then 32 else 128))
    (placed : Option NodeId) (exact : Bool)
    (ambient finalAmbient : Ambient) (finalStore : AipStore)
    (accepted : ((WG.nodePlacement (some rootId) key cidr (if v4 then 32 else 128)).run
      (Source.Aip.store (bump d))).run ambient = .ok (((placed,exact),finalStore),finalAmbient)) :
    Eventually (instructionStep fetch)
      (Walked c names d a (if v4 then 32 else 128) placed exact) ⟨a,Add.entry⟩ := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have room' : insertWindow + A.depth ≤ s.data.regs.rsp.toBitVec.toNat := trunk.sep.room
  have top' : s.data.regs.rsp.toBitVec.toNat + 8 ≤ 2^64 := trunk.sep.top
  have r := trunk.resources
  have slotAt := trunk.slotAt
  have stackAt := trunk.atAdd.stackAt
  obtain ⟨base,named,baseNonzero,rootRead⟩ := root_named trunk.relatedA (if v4 then 32 else 128) rootId
    (by cases v4 <;> simpa [bump] using rootAt)
  have baseLt : base < 2^64 := by
    have range := (loadInt_range _ _ _ _ rootRead).2
    have : ((base : Nat) : Int) < 256^8 := range
    omega
  have baseValue : (BitVec.ofNat 64 base).toNat = base := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseLt]
  have rootWord : a.dmem.loadInt a.regs.rdi.toBitVec 8 = some ((BitVec.ofNat 64 base).toNat : Int) := by
    rw [slotAt, baseValue]
    exact rootRead
  have rootNonzero : BitVec.ofNat 64 base ≠ 0 := by
    intro zero
    have h := congrArg BitVec.toNat zero
    rw [baseValue] at h
    exact baseNonzero h
  have rootApart : ∀ x, InRange a.regs.rdi.toBitVec 8 x → ¬Wide a x ∧ ¬c.writes x := by
    intro x h
    rw [slotAt] at h
    exact trunk.heapWide x (read_heap trunk.table trunk.peers trunk.inArena _ (root_span v4) x h)
  have peer : a.regs.r8.toBitVec ≠ 0 := by
    rw [trunk.atAdd.peer]
    intro zero
    apply trunk.peerNonNull
    show s.data.regs.rcx.toBitVec.toNat = 0
    rw [zero]
    rfl
  have small : (if v4 then 32 else 128) < 256 := by cases v4 <;> decide
  have family : (if v4 then 32 else 128) = 32 ∨ (if v4 then 32 else 128) = 128 := by cases v4 <;> simp
  have belowS (k n : Nat) (hn : n ≤ k) (hk : k ≤ 200) :
      (a.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 k) n).isSome = true :=
    trunk.mapped _ _ (trunk.caller.below.load k n hn hk)
  have localsMapped : ∀ off n : Nat, 8 ≤ off → off+n ≤ 56 →
      (a.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n).isSome = true := by
    intro off n lo hi
    have at' : a.regs.rsp.toBitVec - 104 + .ofNat 64 off =
        s.data.regs.rsp.toBitVec - .ofNat 64 (frameSize v4 + 104 - off) := by
      show a.regs.rsp.toBitVec - BitVec.ofNat 64 104 + _ = _
      rw [stackAt, sub_sub_ofNat, sub_add_ofNat _ _ off (by omega)]
    rw [at']
    exact belowS _ n (by omega) (by omega)
  have run := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch
    (to_header fetch premises.insertion premises.tracePc premises.cmp1 r
      (if v4 then 32 else 128) cidr trunk.atAdd.bits (trunk.atAdd.cidr.trans trunk.cidr) bound small
      peer (BitVec.ofNat 64 base) rootNonzero rootWord rootApart localsMapped trunk.bytesWide))
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro h ⟨⟨atH,mappedH⟩,_,forwardH⟩
  have held := atH.held
  obtain ⟨relatedH,shapeH⟩ := held.related trunk
  have fields := Trie.reconstruct_fields relatedH.trie
  have hBV := held.stackAt trunk
  have r13BV : h.data.regs.r13.toBitVec = s.data.regs.rsp.toBitVec - .ofNat 64 (if v4 then 36 else 48) := by
    rw [held.key, trunk.atAdd.query]
    cases v4 <;> rfl
  have scratchBase : h.data.regs.rsp.toBitVec-48 = a.regs.rsp.toBitVec-144 := by
    rw [held.stack, UInt64.toBitVec_sub]
    show a.regs.rsp.toBitVec-96#64-48#64 = a.regs.rsp.toBitVec-144#64
    bv_omega
  have writesWide (x : BitVec 64) (h' : Placement.Writes h.data.regs.rsp c x) : Wide a x ∨ c.writes x := by
    rcases h' with p | q
    · rw [scratchBase] at p
      exact .inl (wide_low a 56 (by decide) x p)
    · exact .inr q
  have readApart : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ x, span.contains x →
      ¬Placement.Writes h.data.regs.rsp c x := by
    intro span member x inside written
    have out := trunk.heapWide x (read_heap trunk.table trunk.peers trunk.inArena span member x inside)
    exact (writesWide x written).elim out.1 out.2
  have nq : (if v4 then 32 else 128)/8 ≤ (if v4 then 36 else 48) + 8 ∧
      (if v4 then 36 else 48) + 8 ≤ frameSize v4 := by cases v4 <;> decide
  have queryApart : ∀ x, InRange h.data.regs.r13.toBitVec ((if v4 then 32 else 128)/8) x →
      ¬Placement.Writes h.data.regs.rsp c x := by
    intro x hx written
    rw [r13BV] at hx
    rcases writesWide x written with hw | hw
    · exact below_under _ _ _ (insertWindow + A.depth) _ (by omega) (by omega) (by omega) x hx
        (wide_tight trunk.atAdd (insertWindow + A.depth) wide x hw)
    · exact trunk.sep.bytesStack x (writes_bytes hw)
        (below_sub _ _ _ (insertWindow + A.depth) (insertWindow + A.depth + 8) (by omega) (by omega) x hx)
  have savedApart : ∀ x, InRange (h.data.regs.rsp.toBitVec+0x24) 4 x ∨
      InRange (h.data.regs.rsp.toBitVec+0x18) 8 x → ¬Placement.Writes h.data.regs.rsp c x := by
    intro x hx written
    have local' : InRange (a.regs.rsp.toBitVec-104+.ofNat 64 44) 4 x ∨
        InRange (a.regs.rsp.toBitVec-104+.ofNat 64 32) 8 x := by
      rcases hx with p | p
      · exact .inl (by rw [← sp_frame a _ held.stack 36]; exact p)
      · exact .inr (by rw [← sp_frame a _ held.stack 24]; exact p)
    rcases written with p | q
    · rw [scratchBase] at p
      have p0 : InRange (a.regs.rsp.toBitVec-144+.ofNat 64 0) 56 x := by simpa using p
      rcases local' with l | l
      · rw [low_base] at l
        exact InRange.offset_disjoint _ (40+44) 4 0 56 (by omega) (by omega) (.inr (by omega)) x l p0
      · rw [low_base] at l
        exact InRange.offset_disjoint _ (40+32) 8 0 56 (by omega) (by omega) (.inr (by omega)) x l p0
    · rcases local' with l | l
      · exact r.coverageApart x (writes_bytes q) (window_sub a 44 4 (by decide) x l)
      · exact r.coverageApart x (writes_bytes q) (window_sub a 32 8 (by decide) x l)
  have trie := trieHeap_of_facts (root := some rootId) relatedH.trie (Placement.heap_trie shapeH) family keyBound
    (fun id eq => by cases eq; exact rootNode)
  have query : AllowedipsChild.QueryWords h.data.dmem h.data.regs.r13.toBitVec (if v4 then 32 else 128) key := by
    have keyWord := trunk.atAdd.keyWord
    unfold AllowedipsChild.QueryWords
    cases v4
    · simp only [Bool.false_eq_true, ↓reduceIte] at keyWord r13BV ⊢
      rw [r13BV]
      refine ⟨by rw [held.above_load trunk 48 8 (by decide) (by decide)]; exact keyWord.1,?_⟩
      show h.data.dmem.loadInt (s.data.regs.rsp.toBitVec - BitVec.ofNat 64 48 + BitVec.ofNat 64 8) 8 = _
      rw [sub_add_ofNat _ 48 8 (by omega), show (48-8 : Nat) = 40 from rfl,
        held.above_load trunk 40 8 (by decide) (by decide)]
      exact keyWord.2
    · simp only [↓reduceIte] at keyWord r13BV ⊢
      rw [r13BV, held.above_load trunk 36 4 (by decide) (by decide)]
      exact keyWord
  have locals : Placement.LocalFields names h key cidr (if v4 then 32 else 128) a.regs.r8.toNat
      h.data.regs.rsp.toNat (none,some rootId,none) := by
    refine ⟨rfl,rfl,?_,atH.parent,rfl,?_,Placement.register_value atH.r15,atH.width,?_,query⟩
    · rw [atH.rbx]
      exact (Trie.interpretation_of_mem fields.nodeIds named).symm
    · apply Placement.register_value
      rw [held.cidr12, zext32_toNat]
      exact trunk.atAdd.cidr.trans trunk.cidr
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.regs.r8.toNat_lt]
      exact atH.owner
  have frame : Placement.Frame h.data c h.data := by
    refine ⟨held.ready,rfl,rfl,rfl,rfl,?_,?_,fun _ _ => rfl⟩
    · intro n hn
      rw [hBV, sub_sub_ofNat]
      exact mappedH _ _ (belowS _ 8 (by omega) (by omega))
    · intro x read inside
      rw [scratchBase] at inside
      exact trunk.bytesWide x read (wide_low a 56 (by decide) x inside)
  have looped := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch
    (loop_from fetch premises.lookup premises.insertion premises.callbacks premises.cmp1
      relatedH shapeH trie locals atH.pc bound frame readApart queryApart savedApart
      ambient finalAmbient finalStore (placed,exact) accepted))
  apply eventually_weaken (instructionStep fetch) _ _ _ _ looped
  rintro t ⟨⟨⟨_,frameT,pcT,rbxT,openT,relatedT,shapeT⟩,mappedT⟩,_,forwardT⟩
  refine ⟨pcT,held.ofFrame frameT,rbxT,?_,frameT.bits ▸ atH.r15,?_,relatedT,shapeT,
    fun x n hx => mappedT x n (mappedH x n hx),forwardT.trans forwardH⟩
  · intro open'
    obtain ⟨bp,r14⟩ := openT open'
    refine ⟨?_,?_⟩
    · rw [bp, zext32_toNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [r14]
      exact UInt64.ofNat_toNat
  · rw [frameT.stack, ← frameT.memory.loadInt _ 8 (fun i hi h' => savedApart _ (.inr ⟨i,hi,rfl⟩) h')]
    exact atH.owner
end

#print axioms root_named
#print axioms trunk_walked
end C1Trunk
