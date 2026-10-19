import Leanux.Proofs.WG.HandshakeSecurity.ExchangeSend

/-! Actual handshake receive and response suffixes transport the exchange
ledger. Only session and keepalive remain callback contracts; native creators
and consumers are checked at their completed source receipts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open Origins.HandshakeSources
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

private theorem branch_tag (site : Decision) (value : Bool) : H1TagSame (branch site value) := by
  intro initial
  exact hoare_liftAmbient (AmbientM.branch site value) _

macro "exchange_receive_step " h:term : tactic => `(tactic| first
  | (nonce_source_head getDev; exact lift _ (fun history => frame_store history _ getDev_sameWGStore))
  | (nonce_source_head modifyDev; exact lift _ (modify_device _ (fun _ => rfl)))
  | (nonce_source_head Cookies.loadPhase; exact lift _ (fun history => frame_store history _ Cookies.loadPhase_sameStore))
  | (nonce_source_head cookieValidatePacket; exact lift_tag _ (H1HandshakeTagFrames.validate $h _ _ _))
  | (nonce_source_head cookieMessageConsume; exact lift_tag _ (H1HandshakeTagFrames.cookieConsume $h _))
  | (nonce_source_head sendHandshakeCookie; exact lift_tag _ (H1HandshakeTagFrames.cookie $h _ _))
  | (nonce_source_head setPeerEndpointFromSkb; exact lift_tag _ (H1HandshakeTagFrames.endpoint $h _ _))
  | (nonce_source_head timersHandshakeComplete; exact lift_tag _ (H1HandshakeTagFrames.complete $h _ _))
  | (nonce_source_head timersSessionDerived; exact lift_tag _ (H1HandshakeTagFrames.derived $h _))
  | (nonce_source_head timersAnyAuthenticatedPacketReceived; exact lift_tag _ (H1HandshakeTagFrames.deleteTimer $h _ _))
  | (nonce_source_head peerPut; exact lift _ (peer_put _))
  | (nonce_source_head WG.orM; exact lift_tag _ (orM_sameView
      (andM_sameView (branch_tag _ _) (branch_tag _ _))
      (andM_sameView (branch_tag _ _) (branch_tag _ _))))
  | (nonce_source_head WG.andM; exact lift_tag _ (andM_sameView (branch_tag _ _) (branch_tag _ _)))
  | (maintenance_lift_action_head Bind.bind
     exact lift _ (update_peer _ _ (fun _ => Or.inl rfl)))
  | exchange_send_step $h)

open Lean Meta Elab Tactic in
elab "exchange_callback " source:ident " using " proof:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StatePrefixPreserves || target.isAppOf ``StatePrefixEnsures do
    throwError "not a state-prefix contract"
  let args := target.getAppArgs
  let action := (if target.isAppOf ``StatePrefixPreserves then args.back! else args[args.size - 2]!).consumeMData.headBeta
  let .fvar fn := action.getAppFn | throwError "not a callback"
  unless (← fn.getDecl).userName.eraseMacroScopes == source.getId.eraseMacroScopes do
    throwError "different callback"
  evalTactic (← `(tactic| exact $proof _))

theorem response_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames)
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (sessions : ∀ pid, Preserves (session pid)) (pid : PeerId) :
    Preserves (responseWith (ExchangeDriver.receiveOps session keepalive) pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold responseWith
  simp only [ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (nonce_source_head Exchange.createResponse; exact createResponse_checked H1 _)
    | exchange_callback session using sessions
    | exchange_receive_step frames

theorem afterMac_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames)
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (sessions : ∀ pid, Preserves (session pid)) (keepalives : ∀ pid, Preserves (keepalive pid))
    (msg : Key) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Preserves (afterMacWith (ExchangeDriver.receiveOps session keepalive) msg src loaded mac) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold afterMacWith
  simp only [ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (nonce_source_head Exchange.consumeInitiation; exact consumeInitiation_checked H1 _)
    | (nonce_source_head Exchange.consumeResponse; exact consumeResponse_checked H1 _)
    | (nonce_source_head responseWith; exact response_checked H1 frames session keepalive sessions _)
    | exchange_callback session using sessions
    | exchange_callback keepalive using keepalives
    | exchange_receive_step frames

theorem reception_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames)
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (sessions : ∀ pid, Preserves (session pid)) (keepalives : ∀ pid, Preserves (keepalive pid))
    (msg : Key) (src : SkbSource) :
    Preserves (receptionWith (ExchangeDriver.receiveOps session keepalive) msg src) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold receptionWith
  simp only [ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (nonce_source_head afterMacWith; exact afterMac_checked H1 frames session keepalive sessions keepalives _ _ _ _)
    | exchange_receive_step frames

theorem receive_worker_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames)
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (sessions : ∀ pid, Preserves (session pid)) (keepalives : ∀ pid, Preserves (keepalive pid)) :
    Preserves (ExchangeDriver.worker session keepalive) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold ExchangeDriver.worker stepWith
  simp only [ExchangeDriver.receiveOps,AuthenticatedEffects.HandshakeWorker.ops]
  repeat' first
    | (nonce_source_head receptionWith; exact reception_checked H1 frames session keepalive sessions keepalives _ _)
    | exchange_receive_step frames

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
