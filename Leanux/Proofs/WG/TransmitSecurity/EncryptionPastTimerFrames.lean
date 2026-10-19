import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastStagingFrames
import Leanux.Proofs.WG.Queues.TxLiveTimers

/-! Timer and queued-work bookkeeping does not restore a historical packet to
an encryption ring. Keepalive staging is deliberately a separate transport. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem place_timer (pid : PeerId) (timer : PeerTimer) (expires clk : UInt64) (queuedUnit : Option Nat) : SameView view (placeOnWheel pid timer expires clk queuedUnit) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold placeOnWheel
  repeat' first
    | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor view).wp (· = initial))
    | maintenance_store_leaf
    | encryption_past_passive initial

theorem arm_timer (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) : SameView view (armTimer pid timer delay clock) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold armTimer
  repeat' first
    | (rx_retention_head placeOnWheel; exact (place_timer _ _ _ _ _).wp (· = initial))
    | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor view).wp (· = initial))
    | maintenance_store_leaf
    | encryption_past_passive initial

theorem del_timer (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold delTimer
  repeat' first
    | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor view).wp (· = initial))
    | maintenance_store_leaf
    | encryption_past_passive initial

theorem mod_guard (pid : PeerId) : SameView view (modPeerTimerGuard pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor view).wp (· = initial))
    | maintenance_store_leaf
    | encryption_past_passive initial

theorem mod_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) : SameView view (modPeerTimer site pid timer delay) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold modPeerTimer
  repeat' first
    | (rx_retention_head modPeerTimerGuard; exact (mod_guard _).wp (· = initial))
    | (rx_retention_head armTimer; exact (arm_timer _ _ _ _).wp (· = initial))
    | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor view).wp (· = initial))
    | maintenance_store_leaf
    | encryption_past_passive initial

macro "encryption_past_timer " initial:term : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact (del_timer _ _).wp (· = $initial))
  | (rx_retention_head armTimer; exact (arm_timer _ _ _ _).wp (· = $initial))
  | (rx_retention_head modPeerTimer; exact (mod_timer _ _ _ _).wp (· = $initial))
  | (rx_retention_head modPeerTimerGuard; exact (mod_guard _).wp (· = $initial))
  | (rx_retention_head callerJiffies; exact ((callerJiffies_sameWGWorld _).factor view).wp (· = $initial))
  | (rx_retention_head jitterBelowRekeyTimeout; exact ((jitterBelowRekeyTimeout_sameWGWorld _).factor view).wp (· = $initial))
  | (rx_retention_head sendQueuedHandshakeInitiation; exact (queued _ _).wp (· = $initial))
  | maintenance_store_leaf
  | encryption_past_passive $initial)

theorem data_sent (pid : PeerId) : SameView view (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersDataSent
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_timer initial

theorem data_received (pid : PeerId) : SameView view (timersDataReceived pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' encryption_past_timer initial

theorem handshake_complete (pid : PeerId) (site : HiddenSite) : SameView view (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersHandshakeComplete
  repeat' encryption_past_timer initial

theorem session_derived (pid : PeerId) : SameView view (timersSessionDerived pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersSessionDerived
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' encryption_past_timer initial

theorem traversal (pid : PeerId) : SameView view (timersTraversal pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' encryption_past_timer initial

theorem initiated (pid : PeerId) : SameView view (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersHandshakeInitiated
  repeat' encryption_past_timer initial

theorem clear_endpoint (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  repeat' encryption_past_timer initial

theorem purge_staged (pid : PeerId) : SameView view (purgeStagedPackets pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold purgeStagedPackets
  repeat' encryption_past_timer initial

theorem retransmit (pid : PeerId) : SameView view (expiredRetransmitHandshake pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact (clear_endpoint _).wp (· = initial))
    | (rx_retention_head purgeStagedPackets; exact (purge_staged _).wp (· = initial))
    | encryption_past_timer initial

theorem new_handshake (pid : PeerId) : SameView view (expiredNewHandshake pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold expiredNewHandshake
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact (clear_endpoint _).wp (· = initial))
    | (rx_retention_head purgeStagedPackets; exact (purge_staged _).wp (· = initial))
    | encryption_past_timer initial

theorem zero_key (pid : PeerId) : SameView view (expiredZeroKeyMaterial pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact (clear_endpoint _).wp (· = initial))
    | (rx_retention_head purgeStagedPackets; exact (purge_staged _).wp (· = initial))
    | encryption_past_timer initial

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
