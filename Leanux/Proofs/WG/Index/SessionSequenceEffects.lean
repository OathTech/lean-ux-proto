import Leanux.Proofs.WG.Index.SessionSequenceModel
import Init.Data.List.Nat.Range

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Campaign2

theorem sessionAllocationSequence_nil (d : Device) (entry : Snapshot)
    (device : entry.wg.device = some d) (bound : KeypairStoreBounded d) :
    SessionAllocationSequenceFacts d [] [] entry := by
  refine ⟨rfl, rfl, ?_, rfl, by simp [sessionSuccessfulIds], d, device, bound, ?_⟩
  · intro call member; cases member
  · simp

/-- Compose numerical and store facts at the observed original call boundary. -/
theorem sessionAllocationSequence_cons (pid : PeerId) (entry : Snapshot)
    (d next : Device) (ok : Bool) (pids : List PeerId)
    (calls : List SessionAllocationCall) (final : Snapshot)
    (device : entry.wg.device = some d) (bound : KeypairStoreBounded d)
    (cursor : next.nextKeypairId = d.nextKeypairId + (if ok then 1 else 0))
    (tail : SessionAllocationSequenceFacts next pids calls final) :
    SessionAllocationSequenceFacts d (pid :: pids) (⟨pid, entry, ok⟩ :: calls) final := by
  have ids : sessionSuccessfulIds (⟨pid, entry, ok⟩ :: calls) =
      List.range' d.nextKeypairId
        (((⟨pid, entry, ok⟩ :: calls).map SessionAllocationCall.result).count true) := by
    cases ok <;> simp [sessionSuccessfulIds, device, List.range'_succ] <;>
      simpa [sessionSuccessfulIds, cursor] using tail.ids
  refine ⟨?_, ?_, ?_, ids, ?_, ?_⟩
  · simp [tail.peers]
  · simpa using congrArg Nat.succ tail.length
  · intro call member
    rcases List.mem_cons.mp member with same | rest
    · subst call
      exact ⟨d, device, bound, store_bound_absent d bound⟩
    · exact tail.entries call rest
  · rw [ids]
    exact List.nodup_range'
  · obtain ⟨out, present, bounded, advance⟩ := tail.finalBound
    refine ⟨out, present, bounded, ?_⟩
    cases ok <;> simp_all [Nat.add_assoc, Nat.add_comm]

end Leanux.Proofs.WG.Index
