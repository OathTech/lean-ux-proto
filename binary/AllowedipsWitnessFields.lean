import AllowedipsWitnessMemory
namespace Binary.AllowedipsWitness
open TrustBase
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem return_read (width key : Nat) (bound : width ≤ 128) : (memory width key).loadInt 0x400800 8 = some 0x500000 := by
  witness_read

theorem preempt_read (width key : Nat) (bound : width ≤ 128) : (memory width key).loadInt preemptCountAddress 4 = some 512 := by
  witness_read

theorem pending_read (width key : Nat) : (memory width key).loadInt softirqPendingAddress 2 = some 0 := by
  witness_read

theorem task_read (width key : Nat) : (memory width key).loadInt currentTaskAddress 8 = some 0x800000 := by
  witness_read

theorem mode_read (width key : Nat) : (memory width key).loadInt 0x8006e0 4 = some 2 := by
  witness_read

theorem capacity_read (width key : Nat) : (memory width key).loadInt 0x8006e4 4 = some 1024 := by
  witness_read

theorem area_read (width key : Nat) : (memory width key).loadInt 0x8006e8 8 = some 0x900000 := by
  witness_read

theorem softirq_read (width key : Nat) : (memory width key).loadInt 0x800704 4 = some 0 := by
  witness_read

theorem coverage_count_read (width key : Nat) : (memory width key).loadInt 0x900000 8 = some 0 := by
  unfold memory
  rw [load_bytes_zero _ _ _ _ (by simp only [List.length_replicate]; decide)
    (by simp only [List.length_replicate]; decide)]
  decide

theorem count4_read : (memory 32 key4).loadInt (peerAddress 3 + .ofNat 64 Layouts.peer_refcount) 4 = some 1 := by
  witness_read

theorem count6_read : (memory 128 key6).loadInt (peerAddress 4 + .ofNat 64 Layouts.peer_refcount) 4 = some 1 := by
  witness_read

theorem key4_read : Allowedips.NetworkKey (memory 32 key4) keyAddress 32 key4 := by
  refine ⟨(0x0302010a : BitVec 32), ?_, by decide⟩
  witness_read

theorem key6_read : Allowedips.NetworkKey (memory 128 key6) keyAddress 128 key6 := by
  refine ⟨(0x020000fd : BitVec 64), (0x0900000000000000 : BitVec 64), ?_, ?_, by decide⟩
  · witness_read
  · witness_read

#print axioms return_read
#print axioms preempt_read
#print axioms coverage_count_read
#print axioms key4_read
#print axioms key6_read
end Binary.AllowedipsWitness
