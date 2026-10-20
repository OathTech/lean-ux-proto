import AllowedipsWitnessFields
namespace Binary.AllowedipsWitness
open TrustBase
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem bytes_defined (m : Mem 64) (a b : BitVec 64) (n : Nat) (bytes : List UInt8)
    (mapped : (m.loadInt a n).isSome = true) :
    ((m.storeBytes b bytes).loadInt a n).isSome = true := by
  rw [loadInt_defined] at mapped ⊢
  intro i hi
  simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases atByte : (bytes.At b)[a + .ofNat 64 i]? with
  | some _ => rfl
  | none => exact mapped i hi

private theorem node_defined (m : Mem 64) (row : NodeFixture) (a : BitVec 64) (width : Nat)
    (mapped : (m.loadInt a width).isSome = true) :
    ((nodeMemory m row).loadInt a width).isSome = true := by
  unfold nodeMemory
  dsimp only
  split
  · iterate 8 apply storeInt_defined
    exact bytes_defined _ _ _ _ _ mapped
  · iterate 9 apply storeInt_defined
    exact bytes_defined _ _ _ _ _ mapped

private theorem nodes_defined (rows : List NodeFixture) (m : Mem 64) (a : BitVec 64) (width : Nat)
    (mapped : (m.loadInt a width).isSome = true) :
    ((rows.foldl nodeMemory m).loadInt a width).isSome = true := by
  induction rows generalizing m with
  | nil => exact mapped
  | cons row rest ih => exact ih _ (node_defined m row a width mapped)

private theorem peers_defined (ids : List Nat) (m : Mem 64) (a : BitVec 64) (width : Nat)
    (mapped : (m.loadInt a width).isSome = true) :
    ((ids.foldl (fun m pid => m.storeInt (peerAddress pid + .ofNat 64 Layouts.peer_refcount) 4 1) m).loadInt a width).isSome = true := by
  induction ids generalizing m with
  | nil => exact mapped
  | cons id rest ih => exact ih _ (storeInt_defined m a _ width 4 1 mapped)

private theorem zero_at_mapped (base : BitVec 64) (size offset width : Nat)
    (bound : size ≤ 2^64) (inside : offset+width ≤ size) :
    (Mem.loadInt ((List.replicate size (0 : UInt8)).At base)
      (base + .ofNat 64 offset) width).isSome = true := by
  apply (loadInt_defined _ _ _).mpr
  intro i hi
  have atByte := get?_At_idx (List.replicate size (0 : UInt8)) base (offset+i)
    (by omega) (by simpa using bound)
  have rhs : (List.replicate size (0 : UInt8))[offset+i]? = some 0 := by
    simp [ show offset+i < size by omega]
  have address : (base + .ofNat 64 offset) + .ofNat 64 i =
      base + .ofNat 64 (offset+i) := by simp [BitVec.ofNat_add, BitVec.add_assoc]
  have read := (congrArg (fun a => ((List.replicate size (0 : UInt8)).At base).get? a)
    address).trans (atByte.trans rhs)
  exact congrArg Option.isSome read

theorem stack_mapped (width key n : Nat) (bound : n < 18) :
    ((memory width key).loadInt ((0x400800#64) - .ofNat 64 ((n+1)*8)) 8).isSome = true := by
  unfold memory
  apply bytes_defined
  iterate 6 apply storeInt_defined
  apply peers_defined
  apply nodes_defined
  apply bytes_defined
  iterate 2 apply storeInt_defined
  have algebra (a b c : BitVec 64) : (a+b)-c = a+(b-c) := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have address : (0x400800#64) - .ofNat 64 ((n+1)*8) =
      (0x400000#64) + .ofNat 64 (2048-(n+1)*8) := by
    calc
      _ = ((0x400000#64) + .ofNat 64 2048) - .ofNat 64 ((n+1)*8) := rfl
      _ = (0x400000#64) + (.ofNat 64 2048 - .ofNat 64 ((n+1)*8)) := algebra _ _ _
      _ = _ := congrArg ((0x400000#64) + ·)
        (BitVec.ofNat_sub_ofNat_of_le 2048 ((n+1)*8) (by omega) (by omega))

  rw [address]
  exact zero_at_mapped _ 2064 _ 8 (by decide) (by omega)

private theorem bytes_slice_mapped (m : Mem 64) (base : BitVec 64) (bytes : List UInt8)
    (offset width : Nat) (bounded : bytes.length ≤ 2^64) (inside : offset+width ≤ bytes.length) :
    ((m.storeBytes base bytes).loadInt (base + .ofNat 64 offset) width).isSome = true := by
  have loaded := MemoryBytes.loadBytes_store_slice m base bytes bounded offset width inside
  rw [Mem.loadInt, loaded]
  rfl

theorem coverage_mapped (width key word : Nat) (bound : word < 1024) :
    ((memory width key).loadInt ((0x900000#64) + .ofNat 64 (8*word)) 8).isSome = true := by
  unfold memory
  exact bytes_slice_mapped _ (0x900000#64) (List.replicate 8192 0) (8*word) 8
    (by simp only [List.length_replicate]; decide)
    (by simp only [List.length_replicate]; omega)

theorem coverage_at (width key : Nat) (preempt : BitVec 32) :
    AllowedipsCoverageAt coverage preempt (memory width key) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (Option.map (BitVec.ofInt 64)) (task_read width key)
  · intro _
    exact congrArg (Option.map (BitVec.ofInt 32)) (softirq_read width key)
  · intro _
    exact congrArg (Option.map (BitVec.ofInt 32)) (mode_read width key)
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · exact congrArg (Option.map (BitVec.ofInt 32)) (capacity_read width key)
    · exact congrArg (Option.map (BitVec.ofInt 64)) (area_read width key)
    · exact ⟨coverage_mapped width key, 0, by decide,
        congrArg (Option.map (BitVec.ofInt 64)) (coverage_count_read width key)⟩

#print axioms stack_mapped
#print axioms coverage_mapped
#print axioms coverage_at
end Binary.AllowedipsWitness
