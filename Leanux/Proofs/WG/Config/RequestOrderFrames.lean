import Leanux.Proofs.WG.Config.RequestOrderReceiptBridge

/-! Physical state effects used by the request observer's entry and validation proofs. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem entry_effect (attrs : DeviceAttrs) (r : Receipt) (flags : UInt32)
    (kind : r.kind = .updateEntry flags) (valid : Valid attrs r) :
    r.result = 0 ∧ r.after = {r.before with wg := incrementState r.before.wg} := by
  obtain ⟨native,run,same⟩ := valid
  rw [kind] at run same
  rcases native with ⟨value,w,v,a,b⟩
  change Except.ok ((0,{w with dev := w.dev.map fun d =>
    {d with deviceUpdateGen := d.deviceUpdateGen + 1}}),a) =
      Except.ok ((value,v),b) at run
  cases run
  cases same
  exact ⟨rfl,rfl⟩

open Leanux.Proofs.Framing in
theorem Internal.ambient_frame {α : Type} (action : AmbientM α) :
    SameView (id : WGWorld → WGWorld) (liftM action : WG.M α) :=
  SameView.of_wp _ _ (fun initial => hoare_liftAmbient action (fun w => w = initial))

open Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes in
theorem Internal.getDev_frame : SameView (id : WGWorld → WGWorld) getDev := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient ret v after run
  cases device : w.dev with
  | none =>
    simp [getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    simp [getDev,device] at run
    exact run.1.2.symm

open Leanux.Proofs.Framing in
theorem Internal.branch_or_frame (left right : Decision) (a b : Bool) :
    SameView (id : WGWorld → WGWorld) (WG.orM (branch left a) (branch right b)) := by
  unfold WG.orM
  exact Leanux.Proofs.WG.Lifetimes.orM_sameView
    (Internal.ambient_frame (AmbientM.branch left a)) (Internal.ambient_frame (AmbientM.branch right b))

end Leanux.Proofs.WG.Config.RequestOrder
