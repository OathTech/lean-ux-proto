import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionControlFrames

/-! Session receipts and keepalive sends occur on the same shared handshake
source. Its native consumers and all refusal arms carry the entry projection. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Origins.HandshakeSources
open Responder.DriverCuts (hooks)

private theorem logic (loaded : Bool) (mac : MacState) : Observed (liftWGPrefix
    (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
      (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie))))) := by
  apply native
  intro confirmed
  unfold WG.orM WG.andM
  simp only [branch]
  repeat' first
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

private theorem needs (loaded : Bool) (mac : MacState) : Observed (liftWGPrefix
    (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie)))) := by
  apply native
  intro confirmed
  unfold WG.andM
  simp only [branch]
  repeat' first
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

macro "pending_driver_handshake_step " edges:term "," quiet:term "," frames:term : tactic => `(tactic| first
  | (nonce_source_head ite; apply conditional
     all_goals change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _)
  | (nonce_source_head Responder.DriverCuts.session; exact session_observed $edges _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive $quiet _)
  | (nonce_source_head getPeer; exact native _ (fun labels => hoare_consequence (Carrier.get_peer labels _) (fun _ hi => hi) (fun _ _ hi => hi.1)))
  | (nonce_source_head getDev; exact native _ (fun labels => Carrier.store labels getDev_sameWGStore))
  | (nonce_source_head modifyDev
     apply native; intro confirmed
     apply Carrier.modify_device
     all_goals intro d; rfl)
  | (nonce_source_head createResponse; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_create_response _) (($frames).create _)))
  | (nonce_source_head addMacToPacket; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_mac _ _) (($frames).mac _ _)))
  | (nonce_source_head sendBufferToPeer; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_send_buffer _ _) (($frames).send _ _)))
  | (nonce_source_head timersSessionDerived; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_derived _) (($frames).derived _)))
  | (nonce_source_head timersTraversal; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_traversal _) (($frames).traversal _)))
  | (nonce_source_head timersAnyAuthenticatedPacketSent; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_sent _) (($frames).sent _)))
  | (nonce_source_head timersAnyAuthenticatedPacketReceived; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_received _) (($frames).received _)))
  | (nonce_source_head timersHandshakeComplete; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_complete _ _) (($frames).complete _ _)))
  | (nonce_source_head sendHandshakeCookie
     exact native _ (Carrier.cookie (Cookies.sendHandshakeCookie_frame _ _)))
  | (nonce_source_head consumeInitiation; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_initiation _) (($frames).initiation _)))
  | (nonce_source_head consumeResponse; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_response _) (($frames).response _)))
  | (nonce_source_head cookieMessageConsume; exact native _ (Carrier.from_retained (Responder.DriverCuts.carrier_cookie_consume _) (($frames).cookie _)))
  | (nonce_source_head setPeerEndpointFromSkb; exact native _ (Carrier.from_frame (Responder.DriverCuts.carrier_endpoint_skb _ _) (($frames).endpoint _ _)))
  | (nonce_source_head WG.peerPut; exact native _ (fun labels => Carrier.peer_put labels _))
  | (nonce_source_head Cookies.loadPhase; exact native _ (fun labels => Carrier.store labels Cookies.loadPhase_sameStore))
  | (nonce_source_head cookieValidatePacket
     exact native _ (Carrier.cookie (Cookies.cookie_frame_of_view wgStoreView _
       ((cookieValidatePacket_sameCookie _ _ _).factor WGOwnedView.toWGStoreView))))
  | (nonce_source_head WG.orM; exact logic _ _)
  | (nonce_source_head WG.andM; exact needs _ _)
  | (first | nonce_source_head branch | nonce_source_head hiddenClock64 | nonce_source_head invariant
     exact ambient _)
  | (nonce_source_head Pure.pure; exact pure _)
  | (nonce_source_head Bind.bind
     nonce_worker_lift
     apply native; intro confirmed
     apply Carrier.modify_peer
     all_goals intro p; rfl)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (with_reducible intro x; try dsimp only))

theorem handshake_response (edges : H1PendingPromotionEdges) (frames : H1PendingHandshakeFrames) (pid : PeerId) :
    Observed (responseWith (Driver.handshakeOps hooks) pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold responseWith
  simp only [Driver.handshakeOps,hooks]
  repeat' pending_driver_handshake_step edges, (), frames

theorem handshake_after_mac (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames) (frames : H1PendingHandshakeFrames)
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Observed (afterMacWith (Driver.handshakeOps hooks) msg src loaded mac) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold afterMacWith
  simp only [Driver.handshakeOps,hooks]
  repeat' first
    | (nonce_source_head responseWith; exact handshake_response edges frames _)
    | pending_driver_handshake_step edges, quiet, frames

theorem handshake_receive (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames) (frames : H1PendingHandshakeFrames) (msg : List UInt8) (src : SkbSource) :
    Observed (receptionWith (Driver.handshakeOps hooks) msg src) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold receptionWith
  simp only [Driver.handshakeOps,hooks]
  repeat' first
    | (nonce_source_head afterMacWith; exact handshake_after_mac edges quiet frames _ _ _ _)
    | pending_driver_handshake_step edges, quiet, frames

theorem handshake (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames) (frames : H1PendingHandshakeFrames) : Observed (Driver.handshakeObserved hooks) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe (stepWith (Driver.handshakeOps hooks))
  unfold stepWith
  simp only [Driver.handshakeOps,hooks]
  repeat' first
    | (nonce_source_head receptionWith; exact handshake_receive edges quiet frames _ _)
    | pending_driver_handshake_step edges, quiet, frames

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
