import Leanux.Proofs.WG.Noise.InitialSlotCredits

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Initial credits for every slot, including repeated aliases, suffice for
recorded successful session installation and remain available in the final slots.
Other callers' preservation of those credits is a separate obligation. -/
theorem beginSession_initial_slots_projected
    (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (alive : p.isDead = false) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (slots : CurrentSlots.SlotInv (Affiliation.state d))
    (credits : ClearReady d (clearKeys p))
    (allocation clock : List UInt8)
    (allocWidth : allocation.length = 40) (allocSuccess : allocation.headD 2 = 1)
    (clockWidth : clock.length = 8) (rest : List HiddenRecord) :
    Campaign2.Returns (beginSession pid)
      (fun s => (s.wg.device = some d ∧ s.wg.keypairCounter = counter) ∧
        s.ambient.hidden = some (sessionReadyRecords allocation clock rest) ∧
        s.ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun ok s => ok = true ∧ ∃ final, s.wg.device = some final ∧
        SessionEffect pid d p counter ok final s.wg.keypairCounter ∧
        ∃ after, final.peers[pid]? = some after ∧ ClearReady final (clearKeys after)) := by
  intro g ambient pre
  obtain ⟨ok, final, after, run, success, out, device, effect⟩ :=
    beginSession_ready_projected pid d p counter resident accepted alive word hashed
    (sessionReady_of_initial_slots pid d p counter resident slots credits)
      allocation clock allocWidth allocSuccess clockWidth rest g ambient pre
  subst ok
  exact ⟨true, final, after, run, rfl, out, device, effect,
    sessionEffect_preserves_slot_credits pid d out p counter final.keypairCounter resident slots credits effect⟩

end Leanux.Proofs.WG.Noise
