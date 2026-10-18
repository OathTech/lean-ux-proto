import Leanux.Proofs.WG.Index.ConfirmationRetirementEffects
import Leanux.Proofs.WG.Index.ReachedIndexClaims
import Leanux.Proofs.WG.Index.HashSlotRotationClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairCallerClaims
import Leanux.Proofs.WG.Index.ConfirmationClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

theorem receivedWithKeypair_retirement (retired : Reservations)
    (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) (View.RetirementSafe retired)
      (fun _ => View.RetirementSafe retired) := by
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
      have retained := confirmationEffect_deadHashedReserved retired pid received d final p ok
        (pre d device) effect
      intro actual found
      change out.dev = some actual at found
      rw [present] at found
      cases found
      exact retained

theorem receivedWithKeypair_indexCore (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) View.IndexCore
      (fun _ => View.IndexCore) := by
  intro g a result v b pre run
  have tables := receivedWithKeypair_tables pid received g a result v b
    (fun d device => (pre d device).1) run
  have slots := receivedWithKeypair_hashSlots pid received g a result v b
    (fun d device => (pre d device).2.1) run
  have coherent := receivedWithKeypair_owner_coherent pid received g a result v b
    (fun d device => (pre d device).2.2.1) run
  have retired := receivedWithKeypair_retirement [] pid received g a result v b
    (fun d device => (pre d device).2.2.2) run
  exact fun d device => ⟨tables d device,slots d device,coherent d device,retired d device⟩

end Leanux.Proofs.WG.Index
