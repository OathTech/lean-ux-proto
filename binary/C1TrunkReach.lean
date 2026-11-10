import C1TrunkTooLong
/-! Result C1, package 2: `add` on an empty root, from its entry to the
allocator's entry (the CALL at +0x42d executed), under `Trunk`. The two
lemmas about the root word are copied from trial T4 (`T4Boundary`). -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem pointer_none {names : List (Nat × Nat)} {path : String} {a : Nat}
    (h : Trie.pointer names path a = .ok none) : a = 0 := by
  unfold Trie.pointer at h
  split at h
  · rename_i zero
    exact eq_of_beq zero
  · split at h <;> cases h

/-- An empty mirror root is a NULL word in the root slot: read off the
reconstruction, not assumed. -/
theorem root_word {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    (related : Allowedips.Corresponds names o m d) (bits : Nat)
    (empty : (if bits = 32 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = none) :
    m.loadInt (.ofNat 64 (names.table+(if bits = 32 then 0 else 8))) 8 = some 0 := by
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
  · simp only [four,↓reduceIte] at empty ⊢
    rw [t4,empty] at hp4
    have zero := pointer_none hp4
    subst zero
    exact word_loadInt _ _ _ _ _ hw4
  · simp only [four,↓reduceIte] at empty ⊢
    rw [t6,empty] at hp6
    have zero := pointer_none hp6
    subst zero
    exact word_loadInt _ _ _ _ _ hw6

theorem toNat_sub_ofNat (sp : BitVec 64) (k : Nat) (h : k ≤ sp.toNat) :
    (sp - .ofNat 64 k).toNat = sp.toNat - k := by
  have lt := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have small : k % 2^64 = k := Nat.mod_eq_of_lt (by omega)
  rw [small]
  omega

/-- Everything `add` wrote between its entry and a live state. -/
theorem Live.fromEntry {c : Context} {s0 u : MachineData} (live : Live c s0 u) :
    EqualOutside (fun x => Window s0 x ∨ c.writes x) s0.dmem u.dmem := by
  intro x outside
  refine ((memory_frame s0 8 (by decide)) x (fun h => outside (.inl ?_))).trans
    (live.frame x (fun h => outside ?_))
  · rw [frame_base] at h
    exact window_sub s0 8 96 (by decide) x h
  · rcases h with p | cw
    · exact .inl (window_sub s0 0 8 (by decide) x (by simpa using p))
    · exact .inr cw

section
variable {L : Statements.C1.Layout} {A : Allocator} {c : Context} {s : MachineState} {w : World}
  {v4 : Bool} {key cidr pid : Nat} {ra : UInt64} {names : Allowedips.Names}
  {stream : List HiddenRecord} {d : Device} {seq : BitVec 64} {a : MachineData}

/-- The root slot `add` is handed, as an address. -/
theorem Trunk.slotAt (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a) :
    a.regs.rdi.toBitVec = .ofNat 64 (names.table+(if (if v4 then 32 else 128) = 32 then 0 else 8)) := by
  have base : s.data.regs.rdi.toBitVec = .ofNat 64 names.table := by
    rw [trunk.table, ← trunk.tableReg]
    show s.data.regs.rdi.toBitVec = BitVec.ofNat 64 s.data.regs.rdi.toBitVec.toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [trunk.atAdd.slot]
  cases v4
  · show s.data.regs.rdi.toBitVec + 8 = _
    rw [base]
    simp [BitVec.ofNat_add]
  · show s.data.regs.rdi.toBitVec = _
    rw [base]
    simp

theorem Trunk.resources (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a) :
    Resources c a :=
  (entry_base (w := w) (window_wide A) trunk.caller trunk.sep trunk.table trunk.peers trunk.inArena
    trunk.tableReg trunk.related trunk.shape trunk.atAdd trunk.mapped).resources

/-- A heap byte is outside `add`'s frame window and the coverage buffer. -/
theorem Trunk.heapOutside (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (x : BitVec 64) (h : L.Heap x) : ¬Window a x ∧ ¬c.writes x := by
  have fs := frameSize_range v4
  refine ⟨fun hw => trunk.sep.heapStack x h (range_mono _ _ _ (by omega) x
    (window_tight trunk.atAdd (insertWindow + A.depth) (window_wide A) x hw)),trunk.sep.heapWrites x h⟩

/-- The `node_cache` word at `add`'s entry. -/
theorem Trunk.cacheAt (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a) :
    a.dmem.loadInt nodeCacheAddress 8 = some ((BitVec.ofNat 64 L.cache).toNat : Int) ∧
    (BitVec.ofNat 64 L.cache).toNat = L.cache ∧
    ∀ x, InRange nodeCacheAddress 8 x → ¬Window a x ∧ ¬c.writes x := by
  have fs := frameSize_range v4
  have wide := window_wide A
  have read := Trie.readNat_loadInt trunk.cache
  have range := (loadInt_range _ _ _ _ read).2
  have value : (BitVec.ofNat 64 L.cache).toNat = L.cache := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have : ((L.cache : Nat) : Int) < 256^8 := range
      omega)]
  have word : nodeCacheAddress = .ofNat 64 cacheWord := by decide
  have inStack (x : BitVec 64) (h : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
      (insertWindow + A.depth - frameSize v4 + 8) x) :
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth) x :=
    range_mono _ _ _ (by omega) x h
  refine ⟨?_,value,fun x h => ⟨fun hw => ?_,fun hw => ?_⟩⟩
  · rw [value, word, ← trunk.atAdd.frameAt.loadInt _ 8 (fun i hi h => by
      rcases h with h | h | h
      · exact trunk.sep.stackCache _ (below_sub _ _ _ _ _ (by omega) (by omega) _ h) ⟨i,hi,rfl⟩
      · exact trunk.sep.heapCache _ (seq_heap _ trunk.tableReg _ h) ⟨i,hi,rfl⟩
      · exact trunk.sep.writesCache _ h ⟨i,hi,rfl⟩)]
    exact read
  · rw [word] at h
    exact trunk.sep.stackCache x (inStack x (window_tight trunk.atAdd _ wide x hw)) h
  · rw [word] at h
    exact trunk.sep.writesCache x hw h
end

#print axioms root_word
#print axioms Trunk.cacheAt
end C1Trunk
