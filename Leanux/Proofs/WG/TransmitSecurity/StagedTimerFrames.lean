import Leanux.Proofs.WG.TransmitSecurity.StagedPeerViewFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObservedFrames

/-! Timer callbacks update peer metadata while retaining every staged occurrence. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

macro "staged_timer_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor stagedAt) $initial)
  | (rx_retention_head jitterBelowRekeyTimeout; exact ((jitterBelowRekeyTimeout_sameWGWorld _).factor stagedAt) $initial)
  | (rx_retention_head modPeerTimerGuard; exact timer_guard _ $initial)
  | (rx_retention_head armTimer; exact arm _ _ _ _ $initial)
  | (rx_retention_head modPeerTimer; exact modify_timer _ _ _ _ $initial)
  | (rx_retention_head delTimer; exact delete_timer _ _ $initial)
  | staged_exact_step $initial)

theorem data_sent (pid : PeerId) : SameView stagedAt (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold timersDataSent
  simp (config := {zeta := false}) only [branch]
  repeat' staged_timer_step initial

theorem data_received (pid : PeerId) : SameView stagedAt (timersDataReceived pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' staged_timer_step initial

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    SameView stagedAt (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold timersHandshakeComplete
  repeat' staged_timer_step initial

theorem session_derived (pid : PeerId) : SameView stagedAt (timersSessionDerived pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold timersSessionDerived
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' staged_timer_step initial

theorem traversal (pid : PeerId) : SameView stagedAt (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold timersTraversal
  simp only [branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' staged_timer_step initial

end Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
