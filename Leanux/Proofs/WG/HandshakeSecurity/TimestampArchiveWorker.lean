import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveSocketFrames

/-! Native handshake work carries the allocation-indexed timestamp archive
through its recorded initiation write, all refusal paths, session creation and
the actual shared keepalive/staging callback. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Origins.HandshakeSources
set_option maxHeartbeats 600000

private def nativeOps : Ops (WGPrefix TimestampReceipt) :=
  TimestampDriver.ops TimestampDriver.hooks.session (Driver.keepaliveObserved TimestampDriver.hooks)

private theorem conditional (p : Prop) [Decidable p] (a b : WGPrefix TimestampReceipt α)
    (ha : Preserves a) (hb : Preserves b) : Preserves (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

private theorem logic (loaded : Bool) (mac : MacState) : Preserves (liftWGPrefix
    (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
      (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie))))) := by
  apply lift
  intro history
  unfold WG.orM WG.andM
  simp only [branch]
  repeat' archive_timer_step history

private theorem needs (loaded : Bool) (mac : MacState) : Preserves (liftWGPrefix
    (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie)))) := by
  apply lift
  intro history
  unfold WG.andM
  simp only [branch]
  repeat' archive_timer_step history

macro "archive_worker_step" : tactic => `(tactic| first
  | (nonce_source_head ite; apply conditional
     all_goals change StatePrefixPreserves (fun h w _ => StateInv h w) History _)
  | (nonce_source_head beginSession; exact lift _ (session _))
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (nonce_source_head getDev; exact lift _ (fun h => frame_store h _ getDev_sameWGStore))
  | (nonce_source_head modifyDev
     apply lift; intro history
     apply modify_device
     intro d; rfl)
  | (nonce_source_head createResponse; exact lift _ (create_response _))
  | (nonce_source_head addMacToPacket; exact lift _ (mac _ _))
  | (nonce_source_head sendBufferToPeer; exact lift _ (send_buffer _ _))
  | (nonce_source_head timersSessionDerived; exact lift _ (derived _))
  | (nonce_source_head timersTraversal; exact lift _ (traversal _))
  | (nonce_source_head timersAnyAuthenticatedPacketSent; exact lift _ (sent _))
  | (nonce_source_head timersAnyAuthenticatedPacketReceived; exact lift _ (received _))
  | (nonce_source_head timersHandshakeComplete; exact lift _ (complete _ _))
  | (nonce_source_head sendHandshakeCookie
     exact lift _ (cookie_frame (Cookies.sendHandshakeCookie_frame _ _)))
  | (nonce_source_head HandshakeSecurity.consumeObserved; exact consume_history _)
  | (nonce_source_head consumeResponse; exact lift _ (response _))
  | (nonce_source_head cookieMessageConsume; exact lift _ (cookie_consume _))
  | (nonce_source_head setPeerEndpointFromSkb; exact lift _ (endpoint_skb _ _))
  | (nonce_source_head WG.peerPut; exact lift _ (peer_put _))
  | (nonce_source_head Cookies.loadPhase; exact lift _ (fun h => frame_store h _ Cookies.loadPhase_sameStore))
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
     apply lift; intro history
     apply update_peer
     intro p; exact ⟨rfl,rfl⟩)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | split
  | (with_reducible intro x; try dsimp only))

private theorem handshake_response (pid : PeerId) : Preserves (responseWith nativeOps pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold responseWith
  simp only [nativeOps,TimestampDriver.ops,Worker.ops,TimestampDriver.hooks]
  repeat' archive_worker_step

private theorem handshake_after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Preserves (afterMacWith nativeOps msg src loaded mac) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold afterMacWith
  simp only [nativeOps,TimestampDriver.ops,Worker.ops,TimestampDriver.hooks]
  repeat' first
    | (nonce_source_head responseWith; exact handshake_response _)
    | archive_worker_step

private theorem handshake_receive (msg : List UInt8) (src : SkbSource) :
    Preserves (receptionWith nativeOps msg src) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold receptionWith
  simp only [nativeOps,TimestampDriver.ops,Worker.ops,TimestampDriver.hooks]
  repeat' first
    | (nonce_source_head afterMacWith; exact handshake_after_mac _ _ _ _)
    | archive_worker_step

theorem handshake_worker : Preserves (Driver.handshakeObserved TimestampDriver.hooks) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History (stepWith nativeOps)
  unfold stepWith
  simp only [nativeOps,TimestampDriver.ops,Worker.ops,TimestampDriver.hooks]
  repeat' first
    | (nonce_source_head receptionWith; exact handshake_receive _ _)
    | archive_worker_step

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
