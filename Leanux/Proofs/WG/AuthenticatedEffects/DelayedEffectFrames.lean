import Leanux.Proofs.WG.AuthenticatedEffects.TimerOccurrences
import Leanux.Proofs.WG.AuthenticatedEffects.QueuedSourceContracts
import Leanux.Proofs.WG.Queues.WorkQueueFrames

/-! Native cross-frames for the two delayed-effect carriers. Timer arms do not
create work tickets; queue edits do not replace timer wheel occurrences. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Queues.WorkQueueFrames Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem place_queue (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64)
    (unit : Option Nat) : SameView view (placeOnWheel pid timer expires clock unit) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold placeOnWheel
  simp (config := {zeta := false}) only [hidden, invariant, peekHiddenSite]
  repeat' first
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | work_queue_step initial

theorem arm_queue (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    SameView view (armTimer pid timer delay caller) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient, hidden, invariant, unsupported]
  repeat' first
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (fun s => s = initial))
    | (rx_retention_head placeOnWheel; exact (place_queue _ _ _ _ _).wp (fun s => s = initial))
    | work_queue_step initial

theorem delete_queue (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold delTimer
  repeat' work_queue_step initial

theorem queue_factor (w : WGWorld) :
    QueuedOccurrences.queue w = ((view w).map (fun q => q.2.1)).getD [] := by
  simp only [QueuedOccurrences.queue,view,Option.map_map,Function.comp_def]

theorem queue_of_frame {action : WG.M α} (frame : SameView view action) :
    SameView QueuedOccurrences.queue action :=
  frame.of_factor (fun q => (q.map fun q => q.2.1).getD []) QueuedOccurrences.queue queue_factor

theorem queue_edit_timers (f : List PeerId → List PeerId) :
    SameView TimerSlots.view (modifyDev fun d => {d with sendWorkQueue := f d.sendWorkQueue}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases run
  funext pid timer
  cases hd : w.dev <;> simp [TimerSlots.view,hd]

end Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffects
