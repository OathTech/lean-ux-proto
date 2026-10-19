import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceReceive
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveWorker

/-! Exact exchange callbacks receive positive-reference entry states. Cookie
consumption is checked at its native callback without adding a new event. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Origins.HandshakeSources

private def nativeOps : Ops (WGPrefix Exchange.Event) :=
  ExchangeDriver.receiveOps ExchangeDriver.hooks.session (Driver.keepaliveObserved ExchangeDriver.hooks)

private theorem conditional (p : Prop) [Decidable p] (a b : WGPrefix Exchange.Event α)
    (ha : Observed a) (hb : Observed b) : Observed (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

private theorem logic (loaded : Bool) (mac : MacState) : Observed (liftWGPrefix
    (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
      (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie))))) := by
  apply lift
  unfold WG.orM WG.andM
  simp only [branch]
  repeat' peer_reference_timer_step

private theorem needs (loaded : Bool) (mac : MacState) : Observed (liftWGPrefix
    (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie)))) := by
  apply lift
  unfold WG.andM
  simp only [branch]
  repeat' peer_reference_timer_step

macro "peer_reference_worker_step" : tactic => `(tactic| first
  | (nonce_source_head ite; apply conditional
     all_goals change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _)
  | (nonce_source_head Exchange.session; exact session_observed _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (nonce_source_head getDev; exact lift _ (store getDev_sameWGStore))
  | (nonce_source_head modifyDev
     apply lift
     apply modify_device
     intro d; rfl)
  | (nonce_source_head Exchange.createResponse; exact create_response_observed _)
  | (nonce_source_head addMacToPacket; exact lift _ (mac _ _))
  | (nonce_source_head sendBufferToPeer; exact lift _ (send_buffer _ _))
  | (nonce_source_head timersSessionDerived; exact lift _ (derived _))
  | (nonce_source_head timersTraversal; exact lift _ (traversal _))
  | (nonce_source_head timersAnyAuthenticatedPacketSent; exact lift _ (sent _))
  | (nonce_source_head timersAnyAuthenticatedPacketReceived; exact lift _ (received _))
  | (nonce_source_head timersHandshakeComplete; exact lift _ (complete _ _))
  | (nonce_source_head sendHandshakeCookie
     exact lift _ (cookie_frame (Cookies.sendHandshakeCookie_frame _ _)))
  | (nonce_source_head Exchange.consumeInitiation; exact initiation_observed _)
  | (nonce_source_head Exchange.consumeResponse; exact response_observed _)
  | (nonce_source_head cookieMessageConsume; exact lift _ (cookie_consume _))
  | (nonce_source_head setPeerEndpointFromSkb; exact lift _ (endpoint_skb _ _))
  | (nonce_source_head WG.peerPut; exact lift _ (peer_put _))
  | (nonce_source_head Cookies.loadPhase; exact lift _ (store Cookies.loadPhase_sameStore))
  | (nonce_source_head cookieValidatePacket
     exact lift _ (cookie_frame (Cookies.cookie_frame_of_view wgStoreView _
       ((cookieValidatePacket_sameCookie _ _ _).factor WGOwnedView.toWGStoreView))))
  | (nonce_source_head WG.orM; exact logic _ _)
  | (nonce_source_head WG.andM; exact needs _ _)
  | (first | nonce_source_head branch | nonce_source_head hiddenClock64 | nonce_source_head invariant
     exact ambient _)
  | (nonce_source_head Pure.pure; exact pure _)
  | (nonce_source_head Bind.bind
     nonce_worker_lift
     apply lift
     apply update_peer
     intro p positive; exact positive)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (with_reducible intro x; try dsimp only))

private theorem handshake_response (pid : PeerId) : Observed (responseWith nativeOps pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold responseWith
  simp only [nativeOps,ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops,ExchangeDriver.hooks]
  repeat' peer_reference_worker_step

private theorem handshake_after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Observed (afterMacWith nativeOps msg src loaded mac) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold afterMacWith
  simp only [nativeOps,ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops,ExchangeDriver.hooks]
  repeat' first
    | (nonce_source_head responseWith; exact handshake_response _)
    | peer_reference_worker_step

private theorem handshake_receive (msg : List UInt8) (src : SkbSource) :
    Observed (receptionWith nativeOps msg src) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold receptionWith
  simp only [nativeOps,ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops,ExchangeDriver.hooks]
  repeat' first
    | (nonce_source_head afterMacWith; exact handshake_after_mac _ _ _ _)
    | peer_reference_worker_step

theorem handshake_worker : Observed (Driver.handshakeObserved ExchangeDriver.hooks) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe (stepWith nativeOps)
  unfold stepWith
  simp only [nativeOps,ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops,ExchangeDriver.hooks]
  repeat' first
    | (nonce_source_head receptionWith; exact handshake_receive _ _)
    | peer_reference_worker_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
