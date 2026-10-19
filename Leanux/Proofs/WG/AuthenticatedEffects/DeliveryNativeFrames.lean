import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! Native delivery can stop before clearing. Only normal completion implies
the exact final clear; the entry observer separately retains the pre-clear list. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem native_clears : Hoare deliverSent (fun _ => True) (fun _ w => w.wg.sent = []) := by
  have any {α : Type} (action : Leanux.M α) : Hoare action (fun _ => True) (fun _ _ => True) :=
    (hoare_iff_run _ _ _).mpr (fun _ _ _ _ _ => True.intro)
  unfold deliverSent
  apply hoare_bind _ _ (any _)
  intro w
  apply hoare_bind _ _ (any _)
  intro _
  exact hoare_modify _ (fun _ _ => rfl)

theorem delivered_empty (w v : World) (result : Unit)
    (run : deliverSent.run w = .ok (result,v)) : v.wg.sent = [] :=
  (hoare_iff_run _ _ _).mp native_clears w result v True.intro run

end Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
