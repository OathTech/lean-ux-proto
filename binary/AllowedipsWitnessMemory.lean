import AllowedipsSourceWitness
import MemoryBytes
namespace Binary.AllowedipsWitness
open TrustBase
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem load_bytes_away (m : Mem 64) (base a : BitVec 64) (bytes : List UInt8) (width : Nat)
    (apart : ∀ i < width, ¬InRange base bytes.length (a + .ofNat 64 i)) :
    (m.storeBytes base bytes).loadInt a width = m.loadInt a width := by
  have frame : EqualOutside (InRange base bytes.length) m (m.storeBytes base bytes) := by
    intro address outside
    have absent : address ∉ bytes.At base := by
      intro present
      rw [mem_At_iff] at present
      exact outside present
    have missing := Std.ExtHashMap.getElem?_eq_none absent
    simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, missing, Option.none_or]
  exact (frame.loadInt a width apart).symm

theorem load_int_away (m : Mem 64) (base a : BitVec 64) (size width : Nat) (v : Int)
    (apart : ∀ i < width, ¬InRange base size (a + .ofNat 64 i)) :
    (m.storeInt base size v).loadInt a width = m.loadInt a width :=
  ((storeInt_frame m base size v).loadInt a width apart).symm

theorem load_int_same (m : Mem 64) (base : BitVec 64) (size : Nat) (v : Int)
    (bound : size ≤ 2^64) :
    (m.storeInt base size v).loadInt base size = some (v % 2^(8*size)) := by
  have h := MemoryBytes.loadInt_store_subword m base size v bound 0 size (by omega)
  have address : base + .ofNat 64 0 = base := by simp
  rw [address] at h
  simpa using h


theorem load_bytes_zero (m : Mem 64) (base : BitVec 64) (bytes : List UInt8) (width : Nat)
    (bound : bytes.length ≤ 2^64) (inside : width ≤ bytes.length) :
    (m.storeBytes base bytes).loadInt base width = some (Int.ofBytes (bytes.take width)) := by
  have h := MemoryBytes.loadBytes_store_slice m base bytes bound 0 width (by omega)
  have address : base + .ofNat 64 0 = base := by simp
  rw [address] at h
  simpa only [Mem.loadInt, h, List.drop_zero, Option.map_some] using
    congrArg (Option.map Int.ofBytes) h

theorem load_bytes_eight (m : Mem 64) (base : BitVec 64) (bytes : List UInt8) (width : Nat)
    (bound : bytes.length ≤ 2^64) (inside : 8+width ≤ bytes.length) :
    (m.storeBytes base bytes).loadInt (base+8) width = some (Int.ofBytes ((bytes.drop 8).take width)) := by
  exact congrArg (Option.map Int.ofBytes) (MemoryBytes.loadBytes_store_slice m base bytes bound 8 width inside)

macro "witness_apart" : tactic => `(tactic| (
  rintro i hi ⟨j, hj, eq⟩
  have nums := congrArg BitVec.toNat eq
  try simp only [List.length_replicate, List.length_map, List.length_range, Int.toBytes_length, AllowedipsLayout.nodeSize] at hj
  simp [AllowedipsLayout.peer, AllowedipsLayout.bit, AllowedipsLayout.cidr,
    AllowedipsLayout.bits, AllowedipsLayout.bit_at_a, AllowedipsLayout.bit_at_b, AllowedipsLayout.bitlen,
    Layouts.peer_refcount, preemptCountAddress, currentTaskAddress, softirqPendingAddress,
    nodeAddress, peerAddress, keyAddress, AllowedipsLayout.nodeSize,
    BitVec.toNat_add] at nums
  omega))

macro "witness_read" : tactic => `(tactic| (
  try simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  unfold memory
  rw [show List.range 5 = [0,1,2,3,4] from rfl]
  simp only [fixtures, List.foldl_cons, List.foldl_nil]
  repeat first
    | (rw [load_int_same _ _ _ _ (by decide)]; decide)
    | (rw [load_bytes_zero _ _ _ _ (by simp) (by simp)]; decide)
    | (rw [load_bytes_eight _ _ _ _ (by simp) (by simp)]; decide)
    | rw [load_int_away _ _ _ _ _ _ (by witness_apart)]
    | rw [load_bytes_away _ _ _ _ _ (by witness_apart)]
    | (rw [nodeMemory]; try dsimp only [NodeFixture.node]; try simp only [show (32 : Nat) = 32 from rfl, show ¬(128 : Nat) = 32 from by decide, ite_true, ite_false])))

theorem read_test : (memory 32 key4).loadInt (nodeAddress 7 + .ofNat 64 AllowedipsLayout.cidr) 1 = some 0 := by
  witness_read

#print axioms read_test
end Binary.AllowedipsWitness
