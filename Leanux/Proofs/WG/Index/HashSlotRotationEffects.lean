import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Leanux.Proofs.WG.Noise.RotationClaims
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.SessionInvariantEffects
import Leanux.Proofs.WG.Index.SessionSequenceSource

import Leanux.Proofs.WG.Index.HashSlotRotationFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- A general ordered certificate preserves coverage when its computed peer update retains every unreleased old slot. Concrete plans below discharge that pure condition. -/
theorem rotationRun_hashSlotCoverage {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final)
    (p : Peer) (resident : d.peers[pid]? = some p)
    (covered : HashSlotCoverage d)
    (slots : ∀ kid, some kid ∈ clearKeys p → some kid ∉ rotationReleases actions →
      some kid ∈ clearKeys (rotationPeer actions p)) :
    HashSlotCoverage final := by
  intro entry member kid owner
  obtain ⟨old,kept,excluded⟩ := rotationRun_retained_key steps entry kid member owner
  obtain ⟨target,peer,key,found,keyFound,keyPeer,slot⟩ := covered entry old kid owner
  by_cases same : pid = target
  · subst target
    have equal : peer = p := Option.some.inj (found.symm.trans resident)
    subst peer
    exact ⟨pid,rotationPeer actions p,key,rotationRun_peer steps p resident,
      kept.trans keyFound,keyPeer,slots kid slot excluded⟩
  · exact ⟨target,peer,key,(rotationRun_other_peer steps target same).trans found,
      kept.trans keyFound,keyPeer,slot⟩

theorem rotationPlan_retains_slots (p : Peer) (initiator : Bool) (newKey kid : KeypairId)
    (slot : some kid ∈ clearKeys p)
    (unreleased : some kid ∉ rotationReleases (rotationPlan p initiator newKey)) :
    some kid ∈ clearKeys (rotationPeer (rotationPlan p initiator newKey) p) := by
  cases initiator
  · simp only [rotationPlan,Bool.false_eq_true,↓reduceIte,rotateResponder,
      rotationReleases,List.mem_cons,List.not_mem_nil,or_false,not_or] at unreleased
    simp only [clearKeys,List.mem_cons,List.not_mem_nil,or_false] at slot
    rcases slot with next | previous | current
    · exact False.elim (unreleased.1 next)
    · exact False.elim (unreleased.2 previous)
    · simp [rotationPlan,rotateResponder,rotationPeer,RotationWrite.apply,clearKeys,current]
  · by_cases pending : p.keypairNext.isSome
    · simp only [rotationPlan,↓reduceIte,pending,rotateWithNext,
        rotationReleases,List.mem_cons,List.not_mem_nil,or_false,not_or] at unreleased
      simp only [clearKeys,List.mem_cons,List.not_mem_nil,or_false] at slot
      rcases slot with next | previous | current
      · simp [rotationPlan,pending,rotateWithNext,rotationPeer,RotationWrite.apply,clearKeys,next]
      · exact False.elim (unreleased.2 previous)
      · exact False.elim (unreleased.1 current)
    · simp only [rotationPlan,↓reduceIte,pending,Bool.false_eq_true,rotateWithoutNext,
        rotationReleases,List.mem_cons,List.not_mem_nil,or_false] at unreleased
      simp only [clearKeys,List.mem_cons,List.not_mem_nil,or_false] at slot
      rcases slot with next | previous | current
      · have absent : p.keypairNext = none := by
          cases selected : p.keypairNext <;> simp_all
        rw [absent] at next
        cases next
      · exact False.elim (unreleased previous)
      · simp [rotationPlan,pending,rotateWithoutNext,rotationPeer,RotationWrite.apply,clearKeys,current]

theorem confirmationPlan_retains_slots (p : Peer) (received kid : KeypairId)
    (matched : p.keypairNext = some received)
    (slot : some kid ∈ clearKeys p)
    (unreleased : some kid ∉ rotationReleases (confirmationPlan p received)) :
    some kid ∈ clearKeys (rotationPeer (confirmationPlan p received) p) := by
  simp only [confirmationPlan,rotationReleases,List.mem_cons,List.not_mem_nil,or_false] at unreleased
  simp only [clearKeys,List.mem_cons,List.not_mem_nil,or_false] at slot
  rcases slot with next | previous | current
  · simp [confirmationPlan,rotationPeer,RotationWrite.apply,clearKeys,← matched,← next]
  · exact False.elim (unreleased previous)
  · simp [confirmationPlan,rotationPeer,RotationWrite.apply,clearKeys,current]

/-- All three original rotation plans retain coverage, even with aliased slots. The normal certificate supplies every successful put; no static reference budget is assumed. -/
theorem rotationPlan_hashSlotCoverage (pid : PeerId) (d final : Device) (p : Peer)
    (initiator : Bool) (newKey : KeypairId)
    (resident : d.peers[pid]? = some p) (covered : HashSlotCoverage d)
    (steps : RotationRun pid d (rotationPlan p initiator newKey) final) :
    HashSlotCoverage final :=
  rotationRun_hashSlotCoverage steps p resident covered (rotationPlan_retains_slots p initiator newKey)

/-- Both confirmation results preserve coverage; the successful arm retains next as current and immediately unhashes the displaced previous key. -/
theorem confirmationEffect_hashSlotCoverage (pid : PeerId) (received : KeypairId)
    (d final : Device) (p : Peer) (ok : Bool)
    (resident : d.peers[pid]? = some p) (covered : HashSlotCoverage d)
    (effect : ConfirmationEffect pid received d p ok final) :
    HashSlotCoverage final := by
  by_cases matched : p.keypairNext = some received
  · simp only [ConfirmationEffect,matched,↓reduceIte] at effect
    exact rotationRun_hashSlotCoverage effect.2 p resident covered
      (confirmationPlan_retains_slots p received · matched)
  · simp only [ConfirmationEffect,matched,↓reduceIte] at effect
    simpa only [effect.2] using covered

end Leanux.Proofs.WG.Index
