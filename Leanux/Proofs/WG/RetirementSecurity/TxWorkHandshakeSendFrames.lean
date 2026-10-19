import Leanux.Proofs.WG.RetirementSecurity.TxWorkHandshakeFrames

/-! Native handshake sends retain the pending TX actor queue. Socket effects
and handshake work scheduling do not remove data-packet service obligations. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem handshake_socket4_work (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView queued (send4 e cache bytes ds exactRx) :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxWorkSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.TxWork.send4_work) e cache bytes ds exactRx

theorem handshake_socket6_work (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView queued (send6 e cache bytes ds exactRx) :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxWorkSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.TxWork.send6_work) e cache bytes ds exactRx

macro "handshake_send_work " initial:term : tactic => `(tactic| first
  | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w=>queued w=$initial))
  | (rx_retention_head armTimer; exact (armTimer_work _ _ _ _).wp (·=$initial))
  | (rx_retention_head modPeerTimerGuard; exact (modPeerTimerGuard_work _).wp (·=$initial))
  | (rx_retention_head delTimer; exact (delTimer_work _ _).wp (·=$initial))
  | (rx_retention_head modPeerTimer; exact (modPeerTimer_work _ _ _ _).wp (·=$initial))
  | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w=>queued w=$initial))
  | (rx_retention_head send4; exact (handshake_socket4_work _ _ _ _ _).wp (·=$initial))
  | (rx_retention_head send6; exact (handshake_socket6_work _ _ _ _ _).wp (·=$initial))
  | handshake_work_step $initial)

theorem buffer_work (pid : PeerId) (msg : List UInt8) : SameView queued (sendBufferToPeer pid msg) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | handshake_send_work initial

theorem derived_work (pid : PeerId) : SameView queued (timersSessionDerived pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold timersSessionDerived
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | handshake_send_work initial

theorem initiated_work (pid : PeerId) : SameView queued (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold timersHandshakeInitiated
  repeat' first
    | handshake_send_work initial

theorem send_response_work (pid : PeerId) : SameView queued (sendHandshakeResponse pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head timersAnyAuthenticatedPacketSent; unfold timersAnyAuthenticatedPacketSent)
    | (rx_retention_head timersTraversal; exact (timersTraversal_work _).wp (· = initial))
    | (rx_retention_head createResponse; exact (create_response_work _).wp (· = initial))
    | (rx_retention_head addMacToPacket; exact (add_mac_work _ _).wp (· = initial))
    | (rx_retention_head beginSession; exact (session_work _).wp (· = initial))
    | (rx_retention_head timersSessionDerived; exact (derived_work _).wp (· = initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_work _ _).wp (· = initial))
    | handshake_send_work initial

theorem send_initiation_work (pid : PeerId) : SameView queued (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head timersAnyAuthenticatedPacketSent; unfold timersAnyAuthenticatedPacketSent)
    | (rx_retention_head timersTraversal; exact (timersTraversal_work _).wp (· = initial))
    | (rx_retention_head createInitiation; exact (create_initiation_work _).wp (· = initial))
    | (rx_retention_head addMacToPacket; exact (add_mac_work _ _).wp (· = initial))
    | (rx_retention_head timersHandshakeInitiated; exact (initiated_work _).wp (· = initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_work _ _).wp (· = initial))
    | handshake_send_work initial

theorem send_worker_work (pid : PeerId) : SameView queued (handshakeSendWorker pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold handshakeSendWorker
  repeat' first
    | (rx_retention_head sendHandshakeInitiation; exact (send_initiation_work _).wp (· = initial))
    | handshake_send_work initial

end Leanux.Proofs.WG.RetirementSecurity.TxWork
