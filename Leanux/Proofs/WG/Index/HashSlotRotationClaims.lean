import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Leanux.Proofs.WG.Noise.RotationClaims
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.SessionInvariantEffects
import Leanux.Proofs.WG.Index.SessionSequenceSource

import Leanux.Proofs.WG.Index.HashSlotRotationEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

theorem addNewKeypair_hashSlots (pid : PeerId) (newKey : KeypairId)
    (d : Device) (p : Peer) (key : Keypair)
    (resident : d.peers[pid]? = some p) (stored : d.keypairs[newKey]? = some key) :
    Campaign2.Ensures (addNewKeypair pid newKey)
      (fun s => s.wg.device = some d ∧ View.HashSlotsSafe s)
      (fun _ s => View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  obtain ⟨final,present,steps⟩ := addNewKeypair_effect pid newKey d p key
    resident stored g ambient result out after pre.1 run
  have covered := rotationPlan_hashSlotCoverage pid d final p key.iAmTheInitiator newKey
    resident (pre.2 d pre.1) steps
  intro actual device
  change out.dev = some actual at device
  rw [present] at device
  cases device
  exact covered

/-- Every normal original confirmation preserves hashed-key slot coverage. Its actual first read supplies residency; no successful-confirmation or readiness premise is supplied. -/
theorem receivedWithKeypair_hashSlots (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) View.HashSlotsSafe
      (fun _ s => View.HashSlotsSafe s) := by
  intro g ambient ok out after pre run
  cases device : g.dev with
  | none =>
    simp [receivedWithKeypair,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [receivedWithKeypair,getPeer,getDev,device,resident,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨final,present,effect⟩ := receivedWithKeypair_effect pid received d p resident
        g ambient ok out after device run
      have covered := confirmationEffect_hashSlotCoverage pid received d final p ok
        resident (pre d device) effect
      intro actual found
      change out.dev = some actual at found
      rw [present] at found
      cases found
      exact covered

end Leanux.Proofs.WG.Index
