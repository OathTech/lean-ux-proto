import Leanux.Proofs.WG.Config.RequestInputEffects
import Leanux.Proofs.WG.Config.RequestOrderSource
import Leanux.Proofs.WG.Config.PortReadbackFrames

/-! Actual clearing and port frames, paired on the same normal native executions. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

open Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes in
theorem input_frame {α : Type} (attrs : DeviceAttrs) (initial : Campaign2.State)
    (P : WGWorld → Prop) (action : WG.M α)
    (frame : SameView (id : WGWorld → WGWorld) action) :
    StatePrefixPreserves (fun h w _ => InputHistory attrs initial h ∧ P w)
      (InputHistory attrs initial) (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift action (fun _ _ _ point => point.1)
  intro h w ambient ret v after point run
  have same : v = w := (ProjectedAction.iff_run_ambient _ _ _).mp frame
    w ambient ret v after run
  exact ⟨point.1,same ▸ point.2⟩

open Leanux.Proofs.Framing in
theorem input_mark (attrs : DeviceAttrs) (initial : Campaign2.State)
    (P : WGWorld → Prop) (site : Decision) (value : Bool) :
    StatePrefixPreserves (fun h w _ => InputHistory attrs initial h ∧ P w)
      (InputHistory attrs initial) (mark site value) :=
  input_frame attrs initial P _
    ((Internal.ambient_frame (AmbientM.branch site value)).bind
      (fun _ => SameView.pure _ ()))

theorem receipt_nonzero_port_context (attrs : DeviceAttrs) (r : Receipt)
    (valid : Valid attrs r) (port : Nat) (nonzero : port ≠ 0)
    (kind : r.kind = .port port) :
    r.after.wg.portBound = r.before.wg.portBound ∧
      r.after.wg.nlSock7 = r.before.wg.nlSock7 ∧
      r.after.wg.fixtureNetDevices = r.before.wg.fixtureNetDevices := by
  obtain ⟨native,run,same⟩ := valid
  rw [kind] at run same
  have fields := setPort_nonzero_configurationFrame port nonzero
    native.before.portBound native.before.nlSock7 native.before.fixtureNetDevices
    native.before native.ambientBefore native.value native.after native.ambientAfter
    ⟨rfl,rfl,rfl⟩ run
  cases same
  exact fields

end Leanux.Proofs.WG.Config.RequestOrder
