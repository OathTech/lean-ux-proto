import Leanux.Proofs.WG.Noise.ConfirmationSequenceModel
import Leanux.Proofs.WG.Noise.RotationEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem confirmation_true_next_none (pid : PeerId) (id : KeypairId)
    (d final : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (effect : ConfirmationEffect pid id d p true final) :
    ∃ caller, final.peers[pid]? = some caller ∧ caller.keypairNext = none := by
  have found := confirmationEffect_peer pid id d final p true resident effect
  exact ⟨rotationPeer (confirmationPlan p id) p, found, rfl⟩

theorem confirmationSequenceEffect_miss (pid : PeerId) (id : KeypairId)
    (ids : List KeypairId) (d final : Device) (p : Peer) (results : List Bool)
    (miss : p.keypairNext ≠ some id)
    (effect : ConfirmationSequenceEffect pid ids d p results final) :
    ConfirmationSequenceEffect pid (id :: ids) d p (false :: results) final := by
  rcases effect with ⟨values, same, restMiss⟩ | ⟨before, matched, after, input, beforeMiss, hit, values, step, caller⟩
  · left
    refine ⟨?_, same, ?_⟩
    · simp [values, List.replicate_succ]
    · intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact miss
      · exact restMiss other member
  · right
    refine ⟨id :: before, matched, after, ?_, ?_, hit, ?_, step, caller⟩
    · simp [input]
    · intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact miss
      · exact beforeMiss other member
    · simp [values, List.replicate_succ]

theorem confirmationSequenceEffect_length (pid : PeerId) (ids : List KeypairId)
    (d final : Device) (p : Peer) (results : List Bool)
    (effect : ConfirmationSequenceEffect pid ids d p results final) :
    results.length = ids.length := by
  rcases effect with ⟨values, _, _⟩ | ⟨before, matched, after, input, _, _, values, _, _⟩
  · simp [values]
  · simp [values, input]

theorem confirmationSequenceEffect_count (pid : PeerId) (ids : List KeypairId)
    (d final : Device) (p : Peer) (results : List Bool)
    (effect : ConfirmationSequenceEffect pid ids d p results final) :
    results.count true ≤ 1 := by
  rcases effect with ⟨values, _, _⟩ | ⟨before, matched, after, _, _, _, values, _, _⟩
  · simp [values, List.count_replicate]
  · simp [values, List.count_replicate, List.count_append]

end Leanux.Proofs.WG.Noise
