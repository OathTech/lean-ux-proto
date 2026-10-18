import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake

/-! Original handshake socket sends and their timer/work bookkeeping retain
all TX packet records and ordered owning queues, including final peer release. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem socket4_wire (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView txCryptWire (send4 e cache bytes ds exactRx) :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_cryptWire) e cache bytes ds exactRx

theorem socket6_wire (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView txCryptWire (send6 e cache bytes ds exactRx) :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_cryptWire) e cache bytes ds exactRx

theorem socket4_contents (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView txQueueContents (send4 e cache bytes ds exactRx) :=
  contents_factor (ownership_queues ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send4_ownership) e cache bytes ds exactRx))

theorem socket6_contents (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView txQueueContents (send6 e cache bytes ds exactRx) :=
  contents_factor (ownership_queues ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.send6_ownership) e cache bytes ds exactRx))

macro "handshake_send_wire " initial:term : tactic => `(tactic| first
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = $initial))
  | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => txCryptWire w = $initial))
  | (rx_retention_head armTimer; exact (armTimer_cryptWire _ _ _ _).wp (· = $initial))
  | (rx_retention_head modPeerTimerGuard; exact (modPeerTimerGuard_cryptWire _).wp (· = $initial))
  | (rx_retention_head delTimer; exact (delTimer_cryptWire _ _).wp (· = $initial))
  | (rx_retention_head modPeerTimer; exact (modPeerTimer_cryptWire _ _ _ _).wp (· = $initial))
  | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => txCryptWire w = $initial))
  | (rx_retention_head send4; exact (socket4_wire _ _ _ _ _).wp (· = $initial))
  | (rx_retention_head send6; exact (socket6_wire _ _ _ _ _).wp (· = $initial))
  | occurrence_handshake_wire $initial)

macro "handshake_send_contents " initial:term : tactic => `(tactic| first
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => txQueueContents w = $initial))
  | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => txQueueContents w = $initial))
  | (rx_retention_head armTimer; exact (contents_factor (ownership_queues (armTimer_ownership _ _ _ _))).wp (· = $initial))
  | (rx_retention_head modPeerTimerGuard; exact (contents_factor (ownership_queues (modPeerTimerGuard_ownership _))).wp (· = $initial))
  | (rx_retention_head delTimer; exact (contents_factor (ownership_queues (delTimer_ownership _ _))).wp (· = $initial))
  | (rx_retention_head modPeerTimer; exact (contents_factor (ownership_queues (modPeerTimer_ownership _ _ _ _))).wp (· = $initial))
  | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => txQueueContents w = $initial))
  | (rx_retention_head send4; exact (socket4_contents _ _ _ _ _).wp (· = $initial))
  | (rx_retention_head send6; exact (socket6_contents _ _ _ _ _).wp (· = $initial))
  | occurrence_handshake_contents $initial)

theorem buffer_wire (pid : PeerId) (msg : List UInt8) : SameView txCryptWire (sendBufferToPeer pid msg) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | handshake_send_wire initial

theorem derived_wire (pid : PeerId) : SameView txCryptWire (timersSessionDerived pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold timersSessionDerived
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | handshake_send_wire initial

theorem initiated_wire (pid : PeerId) : SameView txCryptWire (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold timersHandshakeInitiated
  repeat' first
    | handshake_send_wire initial

theorem send_response_wire (pid : PeerId) : SameView txCryptWire (sendHandshakeResponse pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head timersAnyAuthenticatedPacketSent; unfold timersAnyAuthenticatedPacketSent)
    | (rx_retention_head timersTraversal; exact (timersTraversal_cryptWire _).wp (· = initial))
    | (rx_retention_head createResponse; exact (OccurrenceKeys.create_response_wire _).wp (· = initial))
    | (rx_retention_head addMacToPacket; exact (OccurrenceKeys.add_mac_wire _ _).wp (· = initial))
    | (rx_retention_head beginSession; exact (OccurrenceKeys.session_wire _).wp (· = initial))
    | (rx_retention_head timersSessionDerived; exact (derived_wire _).wp (· = initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_wire _ _).wp (· = initial))
    | handshake_send_wire initial

theorem send_initiation_wire (pid : PeerId) : SameView txCryptWire (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head timersAnyAuthenticatedPacketSent; unfold timersAnyAuthenticatedPacketSent)
    | (rx_retention_head timersTraversal; exact (timersTraversal_cryptWire _).wp (· = initial))
    | (rx_retention_head createInitiation; exact (OccurrenceKeys.create_initiation_wire _).wp (· = initial))
    | (rx_retention_head addMacToPacket; exact (OccurrenceKeys.add_mac_wire _ _).wp (· = initial))
    | (rx_retention_head timersHandshakeInitiated; exact (initiated_wire _).wp (· = initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_wire _ _).wp (· = initial))
    | handshake_send_wire initial

theorem send_worker_wire (pid : PeerId) : SameView txCryptWire (handshakeSendWorker pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold handshakeSendWorker
  repeat' first
    | (rx_retention_head sendHandshakeInitiation; exact (send_initiation_wire _).wp (· = initial))
    | handshake_send_wire initial

theorem buffer_contents (pid : PeerId) (msg : List UInt8) : SameView txQueueContents (sendBufferToPeer pid msg) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | handshake_send_contents initial

theorem derived_contents (pid : PeerId) : SameView txQueueContents (timersSessionDerived pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold timersSessionDerived
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | handshake_send_contents initial

theorem initiated_contents (pid : PeerId) : SameView txQueueContents (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold timersHandshakeInitiated
  repeat' first
    | handshake_send_contents initial

theorem send_response_contents (pid : PeerId) : SameView txQueueContents (sendHandshakeResponse pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head timersAnyAuthenticatedPacketSent; unfold timersAnyAuthenticatedPacketSent)
    | (rx_retention_head timersTraversal; exact (contents_factor (ownership_queues (timersTraversal_ownership _))).wp (· = initial))
    | (rx_retention_head createResponse; exact (contents_factor (OccurrenceKeys.create_response_queues _)).wp (· = initial))
    | (rx_retention_head addMacToPacket; exact (contents_factor (OccurrenceKeys.add_mac_queues _ _)).wp (· = initial))
    | (rx_retention_head beginSession; exact (contents_factor (OccurrenceKeys.session_queues _)).wp (· = initial))
    | (rx_retention_head timersSessionDerived; exact (derived_contents _).wp (· = initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_contents _ _).wp (· = initial))
    | handshake_send_contents initial

theorem send_initiation_contents (pid : PeerId) : SameView txQueueContents (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head timersAnyAuthenticatedPacketSent; unfold timersAnyAuthenticatedPacketSent)
    | (rx_retention_head timersTraversal; exact (contents_factor (ownership_queues (timersTraversal_ownership _))).wp (· = initial))
    | (rx_retention_head createInitiation; exact (contents_factor (OccurrenceKeys.create_initiation_queues _)).wp (· = initial))
    | (rx_retention_head addMacToPacket; exact (contents_factor (OccurrenceKeys.add_mac_queues _ _)).wp (· = initial))
    | (rx_retention_head timersHandshakeInitiated; exact (initiated_contents _).wp (· = initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_contents _ _).wp (· = initial))
    | handshake_send_contents initial

theorem send_worker_contents (pid : PeerId) : SameView txQueueContents (handshakeSendWorker pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold handshakeSendWorker
  repeat' first
    | (rx_retention_head sendHandshakeInitiation; exact (send_initiation_contents _).wp (· = initial))
    | handshake_send_contents initial

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
