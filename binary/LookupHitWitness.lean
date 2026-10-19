import SourceAdapter
import LookupHitWitnessState
import LookupWitness

namespace Binary.LookupHitWitness
open Leanux Leanux.WG TrustBase
open LookupWitness (coverage load_away range_nat)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

private theorem unchanged (live : Bool) (address : BitVec 64) (width : Nat)
    (separate : ∀ i < width, ¬(InRange (0x300000 : BitVec 64) 8 (address + .ofNat 64 i) ∨
      InRange (0x600420 : BitVec 64) 4 (address + .ofNat 64 i) ∨
      InRange (0x6000e0 : BitVec 64) 8 (address + .ofNat 64 i))) :
    (memory live).loadInt address width = LookupWitness.memory.loadInt address width := by
  unfold memory
  rw [load_away _ _ _ _ _ _ (fun i hi h => separate i hi (.inl h)),
    load_away _ _ _ _ _ _ (fun i hi h => separate i hi (.inr (.inl h))),
    load_away _ _ _ _ _ _ (fun i hi h => separate i hi (.inr (.inr h)))]

theorem head_read (live : Bool) : (memory live).loadInt 0x106068 8 = some 0x6000e8 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.head_read

theorem next_read (live : Bool) : (memory live).loadInt 0x6000e8 8 = some 0 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.next_read

theorem kind_read (live : Bool) : (memory live).loadInt 0x6000f8 4 = some 1 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.kind_read

theorem index_read (live : Bool) : (memory live).loadInt 0x6000fc 4 = some 0x0a0b0c0d := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.index_read

theorem return_read (live : Bool) : (memory live).loadInt 0x400800 8 = some 0x500000 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.return_read

theorem preempt_read (live : Bool) : (memory live).loadInt preemptCountAddress 4 = some 0 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [preemptCountAddress,   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.preempt_read

theorem pending_read (live : Bool) : (memory live).loadInt softirqPendingAddress 2 = some 0 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [  softirqPendingAddress, BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.pending_read

theorem task_read (live : Bool) : (memory live).loadInt currentTaskAddress 8 = some 0x800000 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [ currentTaskAddress,  BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.task_read

theorem mode_read (live : Bool) : (memory live).loadInt 0x8006e0 4 = some 2 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.mode_read

theorem capacity_read (live : Bool) : (memory live).loadInt 0x8006e4 4 = some 1024 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.capacity_read

theorem area_read (live : Bool) : (memory live).loadInt 0x8006e8 8 = some 0x900000 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.area_read

theorem softirq_read (live : Bool) : (memory live).loadInt 0x800704 4 = some 0 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.softirq_read

theorem coverage_count_read (live : Bool) : (memory live).loadInt 0x900000 8 = some 0 := by
  rw [unchanged live _ _ (by
    rintro i hi (h | h | h) <;> obtain ⟨j, hj, equal⟩ := h <;>
      have nums := congrArg BitVec.toNat equal <;>
      simp [   BitVec.toNat_add] at nums <;> omega)]
  exact LookupWitness.coverage_count_read

theorem owner_read (live : Bool) : (memory live).loadInt 0x6000e0 8 = some 0x600000 := by
  unfold memory
  repeat rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [BitVec.toNat_add] at nums
    omega)]
  exact load64_store _ _ (0x600000#64)

theorem count_read (live : Bool) : (memory live).loadInt 0x600420 4 = some (count live : Int) := by
  unfold memory
  rw [load_away _ _ _ _ _ _ (by
    rintro i hi ⟨j, hj, equal⟩
    have nums := congrArg BitVec.toNat equal
    simp [BitVec.toNat_add] at nums
    omega)]
  cases live
  · exact load32_store _ _ (0#32)
  · exact load32_store _ _ (1#32)

theorem output_read (live : Bool) : (memory live).loadInt 0x300000 8 = some 0 :=
  load64_store _ _ (0#64)

theorem coverage_mapped (live : Bool) (word : Nat) (bound : word < 1024) :
    ((memory live).loadInt ((0x900000#64) + .ofNat 64 (8*word)) 8).isSome = true := by
  unfold memory
  iterate 3 apply storeInt_defined
  exact LookupWitness.coverage_mapped word bound

theorem stack_mapped (live : Bool) (n : Nat) (bound : n < 13) :
    ((memory live).loadInt ((0x400800#64) - .ofNat 64 ((n+1)*8)) 8).isSome = true := by
  unfold memory
  iterate 3 apply storeInt_defined
  exact LookupWitness.stack_mapped n bound

theorem callback_state (live : Bool) : KcovState coverage 0 (memory live) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact congrArg (Option.map (BitVec.ofInt 64)) (task_read live)
  · exact congrArg (Option.map (BitVec.ofInt 32)) (mode_read live)
  · exact congrArg (Option.map (BitVec.ofInt 32)) (capacity_read live)
  · exact congrArg (Option.map (BitVec.ofInt 64)) (area_read live)
  · exact congrArg (Option.map (BitVec.ofInt 32)) (softirq_read live)
  · exact congrArg (Option.map (BitVec.ofInt 32)) (preempt_read live)
  · intro _
    exact ⟨coverage_mapped live, 0, by decide, congrArg (Option.map (BitVec.ofInt 64)) (coverage_count_read live)⟩

theorem projected (live : Bool) : LookupRelation.project config (world live) = some (view live) := by
  cases live <;> rfl

theorem physical (live : Bool) : LookupRelation.Physical config [initial live]
    [LookupRelation.entryPoint (data live)] (initial live) (view live) := by
  refine ⟨rfl, ⟨0x6000e8, head_read live, ?_⟩, ?_, ?_⟩
  · change BucketShape (memory live) (0x6000e8#64) [((0x6000e0#64), LookupWitness.entry)]
    exact ⟨by decide, by decide, rfl, by decide, kind_read live, index_read live, 0, next_read live, rfl⟩
  · exact ⟨some 0, rfl, owner_read live⟩
  · exact ⟨count live, rfl, by decide, count_read live⟩

private theorem bucket_location (live : Bool) (a : BitVec 64)
    (read : LookupBucketBytes config (view live) a) :
    (0x106068 ≤ a.toNat ∧ a.toNat < 0x106070) ∨
    (0x6000e8 ≤ a.toNat ∧ a.toNat < 0x600100) := by
  have ranges : InRange (0x106068#64) 8 a ∨
      InRange (0x6000e8#64) 8 a ∨ InRange (0x6000f8#64) 4 a ∨ InRange (0x6000fc#64) 4 a := by
    simpa [LookupBucketBytes, config, LookupWitness.config, view, LookupWitness.entry,
      LookupRelation.ownerAddress, OwnerWord.address, peerHandshakePeerOffset, BucketShapeReads] using read
  rcases ranges with h | h | h | h
  · exact .inl (range_nat _ _ a (by decide) h)
  · have h := range_nat _ _ a (by decide) h; right; omega
  · have h := range_nat _ _ a (by decide) h; right; omega
  · have h := range_nat _ _ a (by decide) h; right; omega

private theorem owner_location (a : BitVec 64) (read : LookupOwnerBytes config a) :
    0x6000e0 ≤ a.toNat ∧ a.toNat < 0x6000e8 := by
  have h : InRange (0x6000e0#64) 8 a := by
    simpa [LookupOwnerBytes, config, LookupWitness.config, LookupRelation.ownerAddress,
      OwnerWord.address, peerHandshakePeerOffset] using read
  exact range_nat _ _ a (by decide) h

private theorem count_location (a : BitVec 64) (read : LookupCountBytes config a) :
    0x600420 ≤ a.toNat ∧ a.toNat < 0x600424 := by
  have h : InRange (0x600420#64) 4 a := by
    simpa [LookupCountBytes, config, LookupWitness.config, Layouts.peer_refcount] using read
  exact range_nat _ _ a (by decide) h

private theorem data_location (live : Bool) (a : BitVec 64)
    (write : LookupDataWrites config (view live) a) :
    (0x6000e0 ≤ a.toNat ∧ a.toNat < 0x6000e8) ∨
    (0x600420 ≤ a.toNat ∧ a.toNat < 0x600424) := by
  rcases write with h | ⟨_, h⟩
  · exact .inl (owner_location a h)
  · exact .inr (count_location a h)

private theorem reads_location (live : Bool) (a : BitVec 64)
    (read : LookupRelation.Reads config (view live) a) :
    (0x106068 ≤ a.toNat ∧ a.toNat < 0x106070) ∨
    (0x6000e0 ≤ a.toNat ∧ a.toNat < 0x600100) ∨
    (0x600420 ≤ a.toNat ∧ a.toNat < 0x600424) := by
  rcases read with h | h | h | h
  · have h := bucket_location live a (.inl h); omega
  · have h := bucket_location live a (.inr h); omega
  · have h := owner_location a h; omega
  · have h := count_location a h; omega

private theorem metadata_location (live : Bool) (a : BitVec 64)
    (read : LookupMetadataBytes coverage 0 (view live) a) :
    (0xffffffff81cc85c0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85c8) ∨
    (0x8006e0 ≤ a.toNat ∧ a.toNat < 0x8006f0) := by
  have noSoft : ¬(LookupSoftRead 0 ∨ LookupSoftRead (512+0)) := by
    unfold LookupSoftRead
    decide
  have mode : LookupModeRead coverage 0 ∨ LookupModeRead coverage (512+0) := .inl trivial
  have buffer : LookupBufferNeeded coverage 0 (view live) := .inl ⟨rfl, mode⟩
  simp only [LookupMetadataBytes, noSoft, false_and, mode, true_and, buffer, false_or] at read
  rcases read with h | h | h | h
  · exact .inl (range_nat 0xffffffff81cc85c0 8 a (by decide) h)
  · have h := range_nat 0x8006e0 4 a (by decide) h; right; omega
  · have h := range_nat 0x8006e4 4 a (by decide) h; right; omega
  · have h := range_nat 0x8006e8 8 a (by decide) h; right; omega

private theorem coverage_location (live : Bool) (a : BitVec 64)
    (write : LookupCoverageWrites coverage 0 (view live) a) :
    0x900000 ≤ a.toNat ∧ a.toNat < 0x902000 :=
  range_nat 0x900000 8192 a (by decide) write.2

private theorem storage_location (_live : Bool) (a : BitVec 64) (read : KcovStorageBytes coverage a) :
    0x900000 ≤ a.toNat ∧ a.toNat < 0x902000 := by
  rcases read with h | h
  · have h := range_nat 0x900000 8 a (by decide) h; omega
  · exact range_nat 0x900000 8192 a (by decide) h

private theorem stack_location (live : Bool) (a : BitVec 64) (write : LookupStackWrites config (initial live) a) :
    0x400798 ≤ a.toNat ∧ a.toNat < 0x400800 :=
  by cases live <;> exact range_nat 0x400798 104 a (by decide) write

private theorem live_stack_location (live : Bool) (a : BitVec 64) (read : LookupLiveStack config (initial live) a) :
    0x400798 ≤ a.toNat ∧ a.toNat < 0x400808 :=
  by cases live <;> exact range_nat 0x400798 112 a (by decide) read

private theorem preempt_location (_live : Bool) (a : BitVec 64) (read : InRange preemptCountAddress 4 a) :
    0xffffffff81cc85c8 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85cc :=
  range_nat 0xffffffff81cc85c8 4 a (by decide) read

private theorem service_location (live : Bool) (a : BitVec 64) (read : LookupServiceBytes coverage 0 (view live) a) :
    (0xffffffff81cc85c0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85cc) ∨
    (0x8006e0 ≤ a.toNat ∧ a.toNat < 0x8006f0) ∨
    (0x900000 ≤ a.toNat ∧ a.toNat < 0x902000) := by
  rcases read with h | h | ⟨_, h⟩
  · have h := metadata_location live a h; omega
  · have h := preempt_location live a h; omega
  · exact .inr (.inr (storage_location live a h))

theorem witness_pre (live : Bool) : Pre_lookup config coverage 0 0x500000 (initial live) (world live) := by
  refine ⟨view live, {
    pc := rfl, frame := ⟨by cases live <;> decide, return_read live⟩, table := rfl, query := rfl
    kinds := ?_, projected := projected live, focus := ⟨rfl, rfl⟩, physical := physical live
    steps := rfl, rxSection := rfl, coverageAt := ?_, preemptAt := (callback_state live).2.1
    stackMapped := stack_mapped live, outputMapped := fun _ => congrArg Option.isSome (output_read live)
    bhHardirq := by decide, bhPending := fun _ => pending_read live
    readsScratch := ?_, serviceStack := ?_, coverageStack := ?_, coverageMetadata := ?_
    coveragePreempt := ?_, bhStack := ?_, bhMetadata := ?_, dataService := ?_
    dataReturn := ?_, dataBucket := ?_, ownerCount := ?_, outputProtected := ?_, pendingFrame := ?_ }⟩
  · intro kind; cases live <;> cases kind <;> rfl
  · refine ⟨(callback_state live).1.1, fun _ => (callback_state live).1.2.2.2.2,
      fun _ => (callback_state live).1.2.1, fun _ => ?_⟩
    exact ⟨(callback_state live).1.2.2.1, (callback_state live).1.2.2.2.1,
      (callback_state live).2.2 (.inl rfl)⟩
  · intro a h bad
    have h := reads_location live a h
    rcases bad with bad | bad | bad
    · have bad := stack_location live a bad; omega
    · have bad := coverage_location live a bad; omega
    · have bad := preempt_location live a bad; omega
  · intro a h bad
    have h := service_location live a h
    have bad := stack_location live a bad
    omega
  · intro a h bad
    have h := coverage_location live a h
    have bad := live_stack_location live a bad
    omega
  · intro a h bad
    have h := coverage_location live a h
    have bad := metadata_location live a bad
    omega
  · intro a h bad
    have h := coverage_location live a h
    have bad := preempt_location live a bad
    omega
  · intro a h bad
    have h := preempt_location live a h
    have bad := live_stack_location live a bad
    omega
  · intro a h bad
    have bad := preempt_location live a bad
    rcases h with h | ⟨_, h⟩
    · have h := metadata_location live a h; omega
    · have h := storage_location live a h; omega
  · intro a h bad
    have h := service_location live a h
    have bad := data_location live a bad
    omega
  · intro a h bad
    have h := range_nat 0x400800 8 a (by decide) h
    have bad := data_location live a bad
    omega
  · intro a h bad
    have h := bucket_location live a h
    have bad := data_location live a bad
    omega
  · intro a h bad
    have h := count_location a h
    have bad := owner_location a bad
    omega
  · intro a h bad
    have h := range_nat 0x300000 8 a (by decide) h.2
    rcases bad with bad | bad | bad | bad
    · have bad := reads_location live a bad; omega
    · have bad := service_location live a bad; omega
    · have loc : 0x4007d0 ≤ a.toNat ∧ a.toNat < 0x400808 := by
        cases live <;> exact range_nat 0x4007d0 56 a (by decide) bad
      omega
    · have bad := coverage_location live a bad; omega
  · intro _ a h bad
    have h := range_nat 0xffffffff81cc85e0 2 a (by decide) h
    rcases bad with bad | bad | bad | bad
    · have bad := stack_location live a bad; omega
    · have bad := coverage_location live a bad; omega
    · have bad := data_location live a bad; omega
    · have bad := range_nat 0x300000 8 a (by decide) bad.2; omega

theorem dead_pre : Pre_lookup config coverage 0 0x500000 (initial false) (world false) := witness_pre false
theorem live_pre : Pre_lookup config coverage 0 0x500000 (initial true) (world true) := witness_pre true

theorem source_accepts (live : Bool) : ∃ answer final,
    (Source.indexLookup config.kinds config.query).run (world live) = .ok (answer, final) := by
  cases live <;> exact ⟨_, _, rfl⟩

#print axioms witness_pre
#print axioms source_accepts
end Binary.LookupHitWitness
