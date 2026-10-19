import Leanux.Proofs.WG.RetirementSecurity.HolderKeepalive

/-! Native endpoint, response-production and timer operations retain the
acquired peer's actual allocation and count. These frames protect the later
caller payment independently from the key-credit transport. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConsume
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem control_peers {action : WG.M α} (same : SameView controlView action) :
    SameView peerView action := same.factor (fun s => s.1.1)

theorem send_view_peers {action : WG.M α}
    (same : SameView (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view) action) :
    SameView peerView action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have view := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  have carrier := ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) v).trans
    ((congrArg (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf) view).trans
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor) w).symm)
  exact congrArg Prod.fst carrier

theorem create_response_peers (pid : PeerId) : SameView peerView (createResponse pid) :=
  send_view_peers ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.create_view) pid)

theorem mac_peers (pid : PeerId) (msg : List UInt8) : SameView peerView (addMacToPacket pid msg) :=
  send_view_peers ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.addMacToPacket_view) pid msg)

theorem buffer_peers (pid : PeerId) (msg : List UInt8) : SameView peerView (sendBufferToPeer pid msg) :=
  send_view_peers ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendBufferToPeer_view) pid msg)

theorem derived_peers (pid : PeerId) : SameView peerView (timersSessionDerived pid) := by
  unfold timersSessionDerived
  exact ((control_peers (modPeerTimer_control _ _ _ _)).map (fun _ => ()))

theorem endpoint_peers (pid : PeerId) (src : SkbSource) : SameView peerView (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w => peerView w = initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (peers_store (endpointFromSkb_sameWGStore _)).wp (·=initial))
    | (rx_retention_head setPeerEndpoint; exact (control_peers (setPeerEndpoint_control _ _)).wp (·=initial))
    | strong_peer_step initial

theorem send_response_peers (pid : PeerId) : SameView peerView (sendHandshakeResponse pid) := by
  intro initial
  change Preserves (fun w => peerView w = initial) _
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createResponse; exact (create_response_peers _).wp (·=initial))
    | (rx_retention_head addMacToPacket; exact (mac_peers _ _).wp (·=initial))
    | (rx_retention_head beginSession; exact (session_peers _).wp (·=initial))
    | (rx_retention_head timersSessionDerived; exact (derived_peers _).wp (·=initial))
    | (rx_retention_head timersTraversal; exact (control_peers (timersTraversal_control _)).wp (·=initial))
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact (control_peers (delTimer_control _ _)).wp (·=initial))
    | (rx_retention_head sendBufferToPeer; exact (buffer_peers _ _).wp (·=initial))
    | strong_peer_step initial

end Leanux.Proofs.WG.RetirementSecurity.HolderConsume
