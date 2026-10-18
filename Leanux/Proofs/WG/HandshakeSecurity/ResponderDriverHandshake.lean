import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHandshakeFrames

/-! Session receipts and keepalive sends occur on the same shared handshake
source. Its native consumers and all refusal arms carry the entry projection. -/
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Origins.HandshakeSources

private theorem conditional (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : Preserves a) (hb : Preserves b) : Preserves (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

private theorem logic (loaded : Bool) (mac : MacState) : Preserves (liftWGPrefix
    (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
      (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie))))) := by
  apply lift
  intro confirmed
  unfold WG.orM WG.andM
  simp only [branch]
  repeat' responder_carrier_poll_step confirmed

private theorem needs (loaded : Bool) (mac : MacState) : Preserves (liftWGPrefix
    (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie)))) := by
  apply lift
  intro confirmed
  unfold WG.andM
  simp only [branch]
  repeat' responder_carrier_poll_step confirmed

macro "responder_driver_handshake_step " H1:term : tactic => `(tactic| first
  | (nonce_source_head ite; apply conditional
     all_goals change StatePrefixPreserves (fun h w _ => Inv h w) Safe _)
  | (nonce_source_head session; exact session_preserves $H1 _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
  | (nonce_source_head getPeer; exact lift _ (carrier_read_peer _))
  | (nonce_source_head getDev; exact lift _ (carrier_store getDev_sameWGStore))
  | (nonce_source_head modifyDev
     apply lift; intro confirmed
     apply carrier_modify
     all_goals intro d; rfl)
  | (nonce_source_head createResponse; exact lift _ (carrier_create_response _))
  | (nonce_source_head addMacToPacket; exact lift _ (carrier_mac _ _))
  | (nonce_source_head sendBufferToPeer; exact lift _ (carrier_send_buffer _ _))
  | (nonce_source_head timersSessionDerived; exact lift _ (carrier_derived _))
  | (nonce_source_head timersTraversal; exact lift _ (carrier_traversal _))
  | (nonce_source_head timersAnyAuthenticatedPacketSent; exact lift _ (carrier_sent _))
  | (nonce_source_head timersAnyAuthenticatedPacketReceived; exact lift _ (carrier_received _))
  | (nonce_source_head timersHandshakeComplete; exact lift _ (carrier_complete _ _))
  | (nonce_source_head sendHandshakeCookie
     exact lift _ (carrier_cookie (Cookies.sendHandshakeCookie_frame _ _)))
  | (nonce_source_head consumeInitiation; exact lift _ (carrier_initiation _))
  | (nonce_source_head consumeResponse; exact lift _ (carrier_response _))
  | (nonce_source_head cookieMessageConsume; exact lift _ (carrier_cookie_consume _))
  | (nonce_source_head setPeerEndpointFromSkb; exact lift _ (carrier_endpoint_skb _ _))
  | (nonce_source_head WG.peerPut; exact lift _ (carrier_peer_put _))
  | (nonce_source_head Cookies.loadPhase; exact lift _ (carrier_store Cookies.loadPhase_sameStore))
  | (nonce_source_head cookieValidatePacket
     exact lift _ (carrier_cookie (Cookies.cookie_frame_of_view wgStoreView _
       ((cookieValidatePacket_sameCookie _ _ _).factor WGOwnedView.toWGStoreView))))
  | (nonce_source_head WG.orM; exact logic _ _)
  | (nonce_source_head WG.andM; exact needs _ _)
  | (first | nonce_source_head branch | nonce_source_head hiddenClock64 | nonce_source_head invariant
     exact ambient _)
  | (nonce_source_head Pure.pure; exact pure _)
  | (nonce_source_head Bind.bind
     nonce_worker_lift
     apply lift; intro confirmed
     apply carrier_update
     all_goals intro p; rfl)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (with_reducible intro x; try dsimp only))

theorem handshake_response (H1 : H1ResponderCurrentEdges) (pid : PeerId) :
    Preserves (responseWith (Driver.handshakeOps hooks) pid) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold responseWith
  simp only [Driver.handshakeOps,hooks]
  repeat' responder_driver_handshake_step H1

theorem handshake_after_mac (H1 : H1ResponderCurrentEdges)
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Preserves (afterMacWith (Driver.handshakeOps hooks) msg src loaded mac) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold afterMacWith
  simp only [Driver.handshakeOps,hooks]
  repeat' first
    | (nonce_source_head responseWith; exact handshake_response H1 _)
    | responder_driver_handshake_step H1

theorem handshake_receive (H1 : H1ResponderCurrentEdges) (msg : List UInt8) (src : SkbSource) :
    Preserves (receptionWith (Driver.handshakeOps hooks) msg src) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold receptionWith
  simp only [Driver.handshakeOps,hooks]
  repeat' first
    | (nonce_source_head afterMacWith; exact handshake_after_mac H1 _ _ _ _)
    | responder_driver_handshake_step H1

theorem handshake (H1 : H1ResponderCurrentEdges) : Preserves (Driver.handshakeObserved hooks) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe (stepWith (Driver.handshakeOps hooks))
  unfold stepWith
  simp only [Driver.handshakeOps,hooks]
  repeat' first
    | (nonce_source_head receptionWith; exact handshake_receive H1 _ _)
    | responder_driver_handshake_step H1

theorem receive_iteration (H1 : H1ResponderCurrentEdges) :
    ProductPreserves (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.2) (product_safe (handshake H1))
    (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
