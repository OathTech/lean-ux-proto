import Leanux.Proofs.WG.RetirementSecurity.TxWorkNativeFrames

/-! Native completion frames for the pending TX actor queue. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem placeOnWheel_work (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : SameView queued (placeOnWheel pid timer expires clk unit) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold placeOnWheel
  simp (config := {zeta := false}) only [peekHiddenSite,hidden,invariant]
  repeat' tx_work_step initial

theorem armTimer_work (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64 := none) : SameView queued (armTimer pid timer delay jc) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | (rx_retention_head placeOnWheel
       exact (placeOnWheel_work _ _ _ _ _).wp (fun s => s = initial))
    | tx_work_step initial

theorem delTimer_work (pid : PeerId) (timer : PeerTimer) :
    SameView queued (delTimer pid timer) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold delTimer
  repeat' tx_work_step initial

theorem modPeerTimerGuard_work (pid : PeerId) :
    SameView queued (modPeerTimerGuard pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold modPeerTimerGuard WG.andM
  simp only [branch]
  repeat' tx_work_step initial

theorem modPeerTimer_work (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) : SameView queued (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).of_factor
    queued queued (fun _ => rfl))
  intro jc
  apply SameView.bind (modPeerTimerGuard_work pid)
  intro ready
  split
  · exact (armTimer_work pid timer delay jc).bind (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

theorem timersTraversal_work (pid : PeerId) :
    SameView queued (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold timersTraversal
  simp only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer
       exact (modPeerTimer_work _ _ _ _).wp (fun s => s = initial))
    | tx_work_step initial
  all_goals exact ((modPeerTimer_work _ _ _ _).map (fun _ => ())).wp (fun s => s = initial)

theorem timersDataSent_work (pid : PeerId) :
    SameView queued (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold timersDataSent
  simp only [branch]
  repeat' first
    | (rx_retention_head callerJiffies
       exact (callerJiffies_sameWGWorld _).wp (fun w => queued w = initial))
    | (rx_retention_head jitterBelowRekeyTimeout
       exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => queued w = initial))
    | (rx_retention_head modPeerTimerGuard
       exact (modPeerTimerGuard_work _).wp (fun s => s = initial))
    | (rx_retention_head armTimer
       exact (armTimer_work _ _ _ _).wp (fun s => s = initial))
    | tx_work_step initial

end Leanux.Proofs.WG.RetirementSecurity.TxWork
