import LookupWitnessState
import LookupEntrySimulation

namespace Binary.LookupWitness
open Leanux TrustBase
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

private theorem load_away (m : Mem 64) (base a : BitVec 64) (width size : Nat) (value : Int)
    (apart : ∀ i < width, ¬InRange base size (a + .ofNat 64 i)) :
    (m.storeInt base size value).loadInt a width = m.loadInt a width :=
  ((storeInt_frame m base size value).loadInt a width apart).symm

theorem head_read : memory.loadInt 0x106068 8 = some 0x6000e8 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load64_store _ _ (0x6000e8#64)

theorem next_read : memory.loadInt 0x6000e8 8 = some 0 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load64_store _ _ (0#64)

theorem kind_read : memory.loadInt 0x6000f8 4 = some 1 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load32_store _ _ (1#32)

theorem index_read : memory.loadInt 0x6000fc 4 = some 0x0a0b0c0d := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load32_store _ _ (0x0a0b0c0d#32)

theorem return_read : memory.loadInt 0x400800 8 = some 0x500000 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load64_store _ _ (0x500000#64)

theorem preempt_read : memory.loadInt preemptCountAddress 4 = some 0 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load32_store _ _ (0#32)

theorem task_read : memory.loadInt currentTaskAddress 8 = some 0x800000 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load64_store _ _ (0x800000#64)

theorem mode_read : memory.loadInt 0x8006e0 4 = some 2 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load32_store _ _ (2#32)

theorem capacity_read : memory.loadInt 0x8006e4 4 = some 1024 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load32_store _ _ (1024#32)

theorem area_read : memory.loadInt 0x8006e8 8 = some 0x900000 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load64_store _ _ (0x900000#64)

theorem softirq_read : memory.loadInt 0x800704 4 = some 0 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load32_store _ _ (0#32)

private theorem load16_zero (m : Mem 64) (a : BitVec 64) :
    (m.storeInt a 2 0).loadInt a 2 = some 0 := by
  have read := loadBytes_store_self m a (Int.toBytes 2 0) (by decide)
  simp only [Int.toBytes_length] at read
  simp only [Mem.storeInt, Mem.loadInt, read]
  rfl

theorem pending_read : memory.loadInt softirqPendingAddress 2 = some 0 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact load16_zero _ _

private theorem zero_load (m : Mem 64) (base : BitVec 64) (size offset width : Nat)
    (bound : size ≤ 2^64) (inside : offset+width ≤ size) :
    (m.storeBytes base (List.replicate size 0)).loadInt (base + .ofNat 64 offset) width = some 0 := by
  have reads (i : Nat) (hi : i < width) :
      (m.storeBytes base (List.replicate size 0)).get?
        ((base + .ofNat 64 offset) + .ofNat 64 i) = some 0 := by
    have atByte := get?_At_idx (List.replicate size (0 : UInt8)) base (offset+i)
      (by omega) (by simpa using bound)
    rw [List.getElem?_replicate, ite_eq_left (by omega)] at atByte
    simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union,
      ← BitVec.add_assoc, ← BitVec.ofNat_add] at atByte ⊢
    have address : (base + .ofNat 64 offset) + .ofNat 64 i =
        base + .ofNat 64 (offset+i) := by simp [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address, atByte]
    rfl
  have mapped : (List.range width).map
      (fun i => (m.storeBytes base (List.replicate size 0)).get?
        ((base + .ofNat 64 offset) + .ofNat 64 i)) = List.replicate width (some (0 : UInt8)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact reads i (by simpa using hi)
  simp only [Mem.loadInt, Mem.loadBytes, mapped]
  have someZeros (n : Nat) : (List.replicate n (some (0 : UInt8))).allSome =
      some (List.replicate n 0) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ, List.allSome, List.mapM_cons] at ih ⊢
      rw [ih]
      rfl
  have zeroBytes (n : Nat) : Int.ofBytes (List.replicate n (0 : UInt8)) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, Int.ofBytes_cons, ih]
  rw [someZeros, Option.map_some, zeroBytes]

theorem coverage_count_read : memory.loadInt 0x900000 8 = some 0 := by
  unfold memory
  iterate 12 rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [preemptCountAddress, currentTaskAddress, softirqPendingAddress,
      BitVec.toNat_add] at nums
    omega)]
  exact zero_load _ _ 8192 0 8 (by decide) (by decide)

theorem coverage_mapped (word : Nat) (bound : word < 1024) :
    (memory.loadInt ((0x900000#64) + .ofNat 64 (8*word)) 8).isSome = true := by
  unfold memory
  iterate 12 apply storeInt_defined
  exact congrArg Option.isSome (zero_load
    ((List.replicate 0x810 (0 : UInt8)).At (0x400000#64))
    (0x900000#64) 8192 (8*word) 8 (by decide) (by omega))

private theorem storeBytes_defined (m : Mem 64) (a b : BitVec 64) (n : Nat) (bytes : List UInt8)
    (mapped : (m.loadInt a n).isSome = true) :
    ((m.storeBytes b bytes).loadInt a n).isSome = true := by
  rw [loadInt_defined] at mapped ⊢
  intro i hi
  simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases atByte : (bytes.At b)[a + .ofNat 64 i]? with
  | some _ => rfl
  | none => exact mapped i hi

private theorem zero_at_mapped (base : BitVec 64) (size offset width : Nat)
    (bound : size ≤ 2^64) (inside : offset+width ≤ size) :
    (Mem.loadInt ((List.replicate size (0 : UInt8)).At base)
      (base + .ofNat 64 offset) width).isSome = true := by
  apply (loadInt_defined _ _ _).mpr
  intro i hi
  have atByte := get?_At_idx (List.replicate size (0 : UInt8)) base (offset+i)
    (by omega) (by simpa using bound)
  have rhs : (List.replicate size (0 : UInt8))[offset+i]? = some 0 := by
    simp [List.getElem?_replicate, show offset+i < size by omega]
  have address : (base + .ofNat 64 offset) + .ofNat 64 i =
      base + .ofNat 64 (offset+i) := by simp [BitVec.ofNat_add, BitVec.add_assoc]
  have read := (congrArg (fun a => ((List.replicate size (0 : UInt8)).At base).get? a)
    address).trans (atByte.trans rhs)
  exact congrArg Option.isSome read

private theorem zero_at_mapped_sub (base : BitVec 64) (size top n : Nat)
    (bound : size < 2^64) (below : (n+1)*8 ≤ top) (inside : top ≤ size) :
    (Mem.loadInt ((List.replicate size (0 : UInt8)).At base)
      ((base + .ofNat 64 top) - .ofNat 64 ((n+1)*8)) 8).isSome = true := by
  have address : ((base + .ofNat 64 top) - .ofNat 64 ((n+1)*8)) =
      base + .ofNat 64 (top-(n+1)*8) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le top ((n+1)*8) (by omega) below]
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [address]
  exact zero_at_mapped base size (top-(n+1)*8) 8 (by omega) (by omega)

private theorem stack_with_bytes_mapped (base : BitVec 64) (size top n : Nat)
    (other : BitVec 64) (bytes : List UInt8)
    (bound : size < 2^64) (below : (n+1)*8 ≤ top) (inside : top ≤ size) :
    (Mem.loadInt (Mem.storeBytes ((List.replicate size (0 : UInt8)).At base) other bytes)
      ((base + .ofNat 64 top) - .ofNat 64 ((n+1)*8)) 8).isSome = true :=
  storeBytes_defined _ _ _ _ _ (zero_at_mapped_sub base size top n bound below inside)

theorem stack_mapped (n : Nat) (bound : n < 6) :
    (memory.loadInt ((0x400800#64) - .ofNat 64 ((n+1)*8)) 8).isSome = true := by
  unfold memory
  iterate 12 apply storeInt_defined
  exact stack_with_bytes_mapped (0x400000#64) 0x810 2048 n (0x900000#64)
    (List.replicate 8192 0) (by decide) (by omega) (by decide)

theorem callback_state : KcovState coverage 0 memory := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact congrArg (Option.map (BitVec.ofInt 64)) task_read
  · exact congrArg (Option.map (BitVec.ofInt 32)) mode_read
  · exact congrArg (Option.map (BitVec.ofInt 32)) capacity_read
  · exact congrArg (Option.map (BitVec.ofInt 64)) area_read
  · exact congrArg (Option.map (BitVec.ofInt 32)) softirq_read
  · exact congrArg (Option.map (BitVec.ofInt 32)) preempt_read
  · intro _
    exact ⟨coverage_mapped, 0, by decide, congrArg (Option.map (BitVec.ofInt 64)) coverage_count_read⟩

theorem projected : LookupRelation.project config world = some view := by rfl

theorem entry_focus : LookupRelation.EntryFocus config view := by
  exact ⟨rfl, rfl⟩

theorem physical : LookupRelation.Physical config [initial]
    [LookupRelation.entryPoint data] initial view := by
  refine ⟨rfl, ⟨0x6000e8, head_read, ?_⟩, rfl, rfl⟩
  change BucketShape memory (0x6000e8#64) [((0x6000e0#64), entry)]
  refine ⟨by decide, by decide, rfl, by decide, kind_read, index_read, 0, next_read, rfl⟩

theorem related : LookupRelation.R config [initial] [LookupRelation.entryPoint data] initial world :=
  LookupRelation.entry_R config world data view projected physical rfl rfl

theorem source_accepts : ∃ final, (WG.indexLookup [.handshake] config.query).run world = .ok (none, final) := by
  exact ⟨_, rfl⟩

private theorem range_nat (base width : Nat) (a : BitVec 64)
    (bound : base+width ≤ 2^64) (inside : InRange (.ofNat 64 base) width a) :
    base ≤ a.toNat ∧ a.toNat < base+width := by
  obtain ⟨i, hi, rfl⟩ := inside
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem reads_location (a : BitVec 64) (read : LookupRelation.Reads config view a) :
    (0x106068 ≤ a.toNat ∧ a.toNat < 0x106070) ∨
    (0x6000e8 ≤ a.toNat ∧ a.toNat < 0x600100) := by
  have ranges : InRange (0x106068#64) 8 a ∨
      InRange (0x6000e8#64) 8 a ∨ InRange (0x6000f8#64) 4 a ∨ InRange (0x6000fc#64) 4 a := by
    simpa [LookupRelation.Reads, config, view, entry, LookupRelation.ownerAddress,
      OwnerWord.address, peerHandshakePeerOffset, BucketShapeReads] using read
  rcases ranges with h | h | h | h
  · exact .inl (range_nat _ _ a (by decide) h)
  · have h := range_nat _ _ a (by decide) h; right; omega
  · have h := range_nat _ _ a (by decide) h; right; omega
  · have h := range_nat _ _ a (by decide) h; right; omega

private theorem metadata_location (a : BitVec 64)
    (read : LookupMetadataBytes coverage 0 view a) :
    (0xffffffff81cc85c0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85c8) ∨
    (0x8006e0 ≤ a.toNat ∧ a.toNat < 0x8006f0) := by
  have noSoft : ¬(LookupSoftRead 0 ∨ LookupSoftRead (512+0)) := by
    unfold LookupSoftRead
    decide
  have mode : LookupModeRead coverage 0 ∨ LookupModeRead coverage (512+0) := .inl trivial
  have buffer : LookupBufferNeeded coverage 0 view := .inl ⟨rfl, mode⟩
  simp only [LookupMetadataBytes, noSoft, false_and, mode, true_and, buffer, false_or] at read
  rcases read with h | h | h | h
  · exact .inl (range_nat 0xffffffff81cc85c0 8 a (by decide) h)
  · have h := range_nat 0x8006e0 4 a (by decide) h; right; omega
  · have h := range_nat 0x8006e4 4 a (by decide) h; right; omega
  · have h := range_nat 0x8006e8 8 a (by decide) h; right; omega

private theorem coverage_location (a : BitVec 64)
    (write : LookupCoverageWrites coverage 0 view a) :
    0x900000 ≤ a.toNat ∧ a.toNat < 0x902000 :=
  range_nat 0x900000 8192 a (by decide) write.2

private theorem storage_location (a : BitVec 64) (read : KcovStorageBytes coverage a) :
    0x900000 ≤ a.toNat ∧ a.toNat < 0x902000 := by
  rcases read with h | h
  · have h := range_nat 0x900000 8 a (by decide) h; omega
  · exact range_nat 0x900000 8192 a (by decide) h

private theorem stack_location (a : BitVec 64) (write : LookupStackWrites config initial a) :
    0x4007d0 ≤ a.toNat ∧ a.toNat < 0x400800 :=
  range_nat 0x4007d0 48 a (by decide) write

private theorem live_stack_location (a : BitVec 64) (read : LookupLiveStack config initial a) :
    0x4007d0 ≤ a.toNat ∧ a.toNat < 0x400808 :=
  range_nat 0x4007d0 56 a (by decide) read

private theorem preempt_location (a : BitVec 64) (read : InRange preemptCountAddress 4 a) :
    0xffffffff81cc85c8 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85cc :=
  range_nat 0xffffffff81cc85c8 4 a (by decide) read

private theorem service_location (a : BitVec 64) (read : LookupServiceBytes coverage 0 view a) :
    (0xffffffff81cc85c0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85cc) ∨
    (0x8006e0 ≤ a.toNat ∧ a.toNat < 0x8006f0) ∨
    (0x900000 ≤ a.toNat ∧ a.toNat < 0x902000) := by
  rcases read with h | h | ⟨_, h⟩
  · have h := metadata_location a h; omega
  · have h := preempt_location a h; omega
  · exact .inr (.inr (storage_location a h))

theorem witness_pre : Pre_lookup config coverage 0 0x500000 initial world := by
  have noData (a : BitVec 64) : ¬LookupDataWrites config view a := by
    simp [LookupDataWrites, LookupOwnerBytes, LookupCountBytes, config, view]
  have noOutput : ¬LookupOutputNeeded view := by simp [LookupOutputNeeded, view]
  refine ⟨view, {
    pc := rfl, frame := ⟨by decide, return_read⟩, table := rfl, query := rfl
    kinds := ?_, projected := projected, focus := entry_focus, physical := physical
    steps := rfl, rxSection := rfl, coverageAt := ?_, preemptAt := callback_state.2.1
    stackMapped := stack_mapped, outputMapped := fun h => False.elim (noOutput h)
    bhHardirq := by decide, bhPending := fun _ => pending_read
    readsScratch := ?_, serviceStack := ?_, coverageStack := ?_, coverageMetadata := ?_
    coveragePreempt := ?_, bhStack := ?_, bhMetadata := ?_, dataService := fun a _ => noData a
    dataReturn := fun a _ => noData a, dataBucket := fun a _ => noData a
    ownerCount := ?_, outputProtected := fun _ h => False.elim (noOutput h.1)
    pendingFrame := ?_ }⟩
  · intro kind; cases kind <;> rfl
  · refine ⟨callback_state.1.1, fun _ => callback_state.1.2.2.2.2,
      fun _ => callback_state.1.2.1, fun _ => ?_⟩
    exact ⟨callback_state.1.2.2.1, callback_state.1.2.2.2.1, callback_state.2.2 (.inl rfl)⟩
  · intro a h bad
    have h := reads_location a h
    rcases bad with bad | bad | bad
    · have bad := stack_location a bad; omega
    · have bad := coverage_location a bad; omega
    · have bad := preempt_location a bad; omega
  · intro a h bad
    have h := service_location a h
    have bad := stack_location a bad
    omega
  · intro a h bad
    have h := coverage_location a h
    have bad := live_stack_location a bad
    omega
  · intro a h bad
    have h := coverage_location a h
    have bad := metadata_location a bad
    omega
  · intro a h bad
    have h := coverage_location a h
    have bad := preempt_location a bad
    omega
  · intro a h bad
    have h := preempt_location a h
    have bad := live_stack_location a bad
    omega
  · intro a h bad
    have bad := preempt_location a bad
    rcases h with h | ⟨_, h⟩
    · have h := metadata_location a h; omega
    · have h := storage_location a h; omega
  · intro a h
    simp [LookupCountBytes, config] at h
  · intro _ a h bad
    have h := range_nat 0xffffffff81cc85e0 2 a (by decide) h
    rcases bad with bad | bad | bad | bad
    · have bad := stack_location a bad; omega
    · have bad := coverage_location a bad; omega
    · exact noData a bad
    · exact noOutput bad.1

#print axioms witness_pre
#print axioms projected
#print axioms entry_focus
#print axioms physical
#print axioms related
#print axioms source_accepts
#print axioms head_read
#print axioms pending_read
#print axioms callback_state
#print axioms stack_mapped
end Binary.LookupWitness
