import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeferred

/-! Exact full-packet frames for native timer callbacks that do not stage
keepalives. Keepalive callbacks intentionally require the staging transport. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimers
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceHandshake

theorem clear_endpoint_wire (pid : PeerId) : SameView txCryptWire (clearPeerEndpointSrc pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset
       exact ((pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames.«0».Leanux.Proofs.WG.RetirementSecurity.dstCacheReset_cryptWire) _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem purge_wire (pid : PeerId) : SameView txCryptWire (purgeStagedPackets pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold purgeStagedPackets
  repeat' crypt_wire_step initial

macro "occurrence_timer_wire " initial:term : tactic => `(tactic| first
  | (rx_retention_head clearPeerEndpointSrc; exact (clear_endpoint_wire _).wp (· = $initial))
  | (rx_retention_head purgeStagedPackets; exact (purge_wire _).wp (· = $initial))
  | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_cryptWire _ _).wp (· = $initial))
  | (rx_retention_head peerGet; exact (peerGet_cryptWire _).wp (· = $initial))
  | handshake_send_wire $initial)

theorem retransmit_wire (pid : PeerId) : SameView txCryptWire (expiredRetransmitHandshake pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold expiredRetransmitHandshake
  simp (config := {zeta := false}) only [branch,branchCmp,Functor.discard,map_const,
    Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' occurrence_timer_wire initial

theorem new_handshake_wire (pid : PeerId) : SameView txCryptWire (expiredNewHandshake pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold expiredNewHandshake
  repeat' occurrence_timer_wire initial

theorem expired_zero_wire (pid : PeerId) : SameView txCryptWire (expiredZeroKeyMaterial pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold expiredZeroKeyMaterial
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' occurrence_timer_wire initial

theorem callback_wire (pid : PeerId) (timer : PeerTimer)
    (notKeepalive : timer ≠ .sendKeepalive) (notPersistent : timer ≠ .persistentKeepalive) :
    SameView txCryptWire (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact retransmit_wire pid
  | sendKeepalive => exact False.elim (notKeepalive rfl)
  | newHandshake => exact new_handshake_wire pid
  | zeroKeyMaterial => exact expired_zero_wire pid
  | persistentKeepalive => exact False.elim (notPersistent rfl)

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimers
