import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionGeometry

/-! Actual completion timers preserve skb allocation geometry and full packet
records through their clock, guard, wheel and peer metadata operations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionGeometry
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity.StagingOccurrences (geometry)

macro "completion_timer_geometry_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | completion_socket_geometry_step $initial)

theorem placeOnWheel_geometry (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : SameView geometry (placeOnWheel pid timer expires clk unit) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold placeOnWheel
  simp (config := {zeta := false}) only [peekHiddenSite,hidden,invariant]
  repeat' completion_timer_geometry_step initial

theorem armTimer_geometry (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64 := none) : SameView geometry (armTimer pid timer delay jc) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | (rx_retention_head placeOnWheel
       exact (placeOnWheel_geometry _ _ _ _ _).wp (fun s => s = initial))
    | completion_timer_geometry_step initial

theorem delTimer_geometry (pid : PeerId) (timer : PeerTimer) :
    SameView geometry (delTimer pid timer) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold delTimer
  repeat' completion_timer_geometry_step initial

theorem modPeerTimerGuard_geometry (pid : PeerId) :
    SameView geometry (modPeerTimerGuard pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold modPeerTimerGuard WG.andM
  simp only [branch]
  repeat' completion_timer_geometry_step initial

theorem modPeerTimer_geometry (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) : SameView geometry (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).of_factor
    geometry geometry (fun _ => rfl))
  intro jc
  apply SameView.bind (modPeerTimerGuard_geometry pid)
  intro ready
  split
  · exact (armTimer_geometry pid timer delay jc).bind (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

theorem timersTraversal_geometry (pid : PeerId) :
    SameView geometry (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersTraversal
  simp only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer
       exact (modPeerTimer_geometry _ _ _ _).wp (fun s => s = initial))
    | completion_timer_geometry_step initial
  all_goals exact ((modPeerTimer_geometry _ _ _ _).map (fun _ => ())).wp (fun s => s = initial)

theorem timersDataSent_geometry (pid : PeerId) :
    SameView geometry (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersDataSent
  simp only [branch]
  repeat' first
    | (rx_retention_head callerJiffies
       exact (callerJiffies_sameWGWorld _).wp (fun w => geometry w = initial))
    | (rx_retention_head jitterBelowRekeyTimeout
       exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => geometry w = initial))
    | (rx_retention_head modPeerTimerGuard
       exact (modPeerTimerGuard_geometry _).wp (fun s => s = initial))
    | (rx_retention_head armTimer
       exact (armTimer_geometry _ _ _ _).wp (fun s => s = initial))
    | completion_timer_geometry_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionGeometry
