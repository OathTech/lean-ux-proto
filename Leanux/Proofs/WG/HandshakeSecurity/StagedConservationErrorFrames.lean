import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationErrorSource
import Leanux.Proofs.WG.Queues.RxStackFrames

/-! Native counter frames before a transmit error charge. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Packets Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem store_errors {action : WG.M α} (frame : SameWGStore action) :
    SameView errors action :=
  frame.of_factor (fun s => s.dev.map Device.txErrors) errors (fun _ => rfl)

theorem notification_frame (family : Nat) (first : Packet) :
    SameView errors (errorNotify family first) := by
  apply SameView.of_wp
  intro initial
  have ambient {α : Type} (action : AmbientM α) :
      Preserves (fun w => errors w = initial) (monadLift action : WG.M α) :=
    hoare_liftAmbient action _
  have routing {α : Type} (action : Net.M α) :
      Preserves (fun w => errors w = initial) (monadLift action : WG.M α) :=
    (store_errors (liftRouting_sameWGStore action)).wp (· = initial)
  have loopback (sites : List HiddenSite) (raised : Bool) :
      Preserves (fun w => errors w = initial) (loopbackSend sites raised) :=
    (store_errors (loopbackSend_kernel sites raised)).wp (· = initial)
  change Preserves (fun w => errors w = initial) (errorNotify family first)
  unfold errorNotify
  simp only [branch,skipCutSites]
  repeat' first
    | (rx_retention_head loopbackSend; exact loopback _ _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact routing _)
    | rx_retention_step


end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
