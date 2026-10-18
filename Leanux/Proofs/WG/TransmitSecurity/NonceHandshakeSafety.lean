import Leanux.Proofs.WG.TransmitSecurity.NonceHandshake

/-! Allocation non-reuse through the original handshake worker, with the
actual session and keepalive callbacks and a history retained on Stop. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Handshake
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Origins.HandshakeSources Frames

private theorem logic (loaded : Bool) (mac : MacState) :
    SameView view (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
      (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie)))) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold WG.orM WG.andM
  simp only [branch]
  repeat' nonce_frame_step initial

private theorem needs (loaded : Bool) (mac : MacState) :
    SameView view (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie))) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold WG.andM
  simp only [branch]
  repeat' nonce_frame_step initial

private theorem conditional {α : Type} (p : Prop) [Decidable p]
    (a b : WGPrefix Allocation α)
    (ha : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup a)
    (hb : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup b) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte] <;> assumption

private theorem modify_peer (pid : PeerId) (f : Peer → Peer) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup
      (liftWGPrefix (do setPeer pid (f (← getPeer pid)))) :=
  Frames.lift_frame ((Frames.peer_read pid).bind fun p => Frames.peer_write pid (f p))

private theorem pure_safe {α : Type} (x : α) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (pure x : WGPrefix Allocation α) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi)

open Lean Meta Elab Tactic in
elab "nonce_worker_lift" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := t.getAppArgs
  let action := if t.isAppOf ``StatePrefixPreserves then args.back! else args[args.size-2]!
  unless action.consumeMData.isAppOf ``liftWGPrefix do throwError "not a native lift"

macro "nonce_worker_step" : tactic => `(tactic| first
  | (nonce_source_head ite; apply conditional)
  | (nonce_source_head keepaliveObserved; exact keepaliveObserved_safe _)
  | (nonce_source_head beginSession; exact Frames.lift_preserves (Frames.begin_session _))
  | (nonce_source_head getPeer; exact Frames.lift_frame (Frames.peer_read _))
  | (nonce_source_head setPeer; exact Frames.lift_frame (Frames.peer_write _ _))
  | (nonce_source_head getDev; exact Frames.lift_frame Frames.device_read)
  | (nonce_source_head modifyDev; exact Frames.lift_frame (Frames.update _ (fun _ => rfl)))
  | (nonce_source_head createResponse; exact Frames.lift_frame (Frames.create_response _))
  | (nonce_source_head addMacToPacket; exact Frames.lift_frame (Frames.mac _ _))
  | (nonce_source_head sendBufferToPeer; exact Frames.lift_frame (Frames.send_buffer _ _))
  | (nonce_source_head timersSessionDerived; exact Frames.lift_frame (Frames.derived _))
  | (nonce_source_head timersTraversal; exact Frames.lift_frame (Frames.traversal _))
  | (nonce_source_head timersAnyAuthenticatedPacketSent; exact Frames.lift_frame (Frames.sent _))
  | (nonce_source_head timersAnyAuthenticatedPacketReceived; exact Frames.lift_frame (Frames.received _))
  | (nonce_source_head timersHandshakeComplete; exact Frames.lift_frame (Frames.complete _ _))
  | (nonce_source_head sendHandshakeCookie; exact Frames.lift_frame (Frames.cookie_send _ _))
  | (nonce_source_head consumeInitiation; exact Frames.lift_preserves (Frames.initiation _))
  | (nonce_source_head consumeResponse; exact Frames.lift_preserves (Frames.response _))
  | (nonce_source_head cookieMessageConsume; exact Frames.lift_preserves (Frames.cookie_consume _))
  | (nonce_source_head setPeerEndpointFromSkb; exact Frames.lift_preserves (Frames.endpoint _ _))
  | (nonce_source_head WG.peerPut; exact Frames.lift_frame (Frames.peerPut _))
  | (nonce_source_head Cookies.loadPhase; exact Frames.lift_frame Frames.load)
  | (nonce_source_head cookieValidatePacket; exact Frames.lift_frame (Frames.cookie_validate _ _ _))
  | (nonce_source_head WG.orM; exact Frames.lift_frame (logic _ _))
  | (nonce_source_head WG.andM; exact Frames.lift_frame (needs _ _))
  | (nonce_source_head branch; exact Frames.lift_frame (Frames.ambient _))
  | (nonce_source_head hiddenClock64; exact Frames.lift_frame (Frames.ambient _))
  | (nonce_source_head invariant; exact Frames.lift_frame (Frames.ambient _))
  | (nonce_source_head Pure.pure
     exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.nodup) (fun _ _ _ hi => hi))
  | (nonce_source_head Bind.bind; nonce_worker_lift; exact modify_peer _ _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head pure; exact pure_safe _)
  | split
  | (with_reducible intro x; try dsimp only))

theorem response_safe (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (responseWith ops pid) := by
  unfold responseWith
  simp only [ops]
  repeat' nonce_worker_step

theorem afterMac_safe (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (afterMacWith ops msg src loaded mac) := by
  unfold afterMacWith
  simp only [ops]
  repeat' first
    | (nonce_source_head responseWith; exact response_safe _)
    | nonce_worker_step

theorem reception_safe (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup (receptionWith ops msg src) := by
  unfold receptionWith
  simp only [ops]
  repeat' first
    | (nonce_source_head afterMacWith; exact afterMac_safe _ _ _ _)
    | nonce_worker_step

theorem safe : StatePrefixPreserves (fun h w _ => Inv (view w) h) List.Nodup observed := by
  unfold observed stepWith
  simp only [ops]
  repeat' first
    | (nonce_source_head receptionWith; exact reception_safe _ _)
    | nonce_worker_step

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Handshake
