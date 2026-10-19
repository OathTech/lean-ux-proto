import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCookieNested

/-! The actual queued receiver retains the validity of its popped input.
Its native frame is derived by exact operation projections, while cookie
history follows the same captured MAC input and failure-retaining callback. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity AuthenticatedEffects
open CausalJournal CookieInput HandshakeSecurity Origins.HandshakeSources
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem receiver_old
    (sg : PeerId→WGPrefix Event Bool) (st : PeerId→WGPrefix TransmitSecurity.Journal.Event Bool)
    (kg : PeerId→WGPrefix Event Unit) (kt : PeerId→WGPrefix TransmitSecurity.Journal.Event Unit)
    (hs : ∀pid,StateProjectsPrefix old? id (sg pid) (st pid))
    (hk : ∀pid,StateProjectsPrefix old? id (kg pid) (kt pid)) (msg : Key) (src : SkbSource) :
    StateProjectsPrefix old? id (receiver sg kg msg src)
      (HandshakeWorker.observedReceive TransmitSecurity.Journal.Event.handshake TransmitSecurity.Journal.handshake?
        st kt msg src) := by
  rw [HandshakeWorker.observedReceive_factor,←CookieConsumption.receive_native]
  apply CookieConsumption.receive_projects old? _ _ _ _
  · intro msg
    unfold NestedPeerRelease.cookieObserved
    apply HandshakeSecurity.Exchange.receipt_ignored old? _ _ _ ?_ (fun _ => rfl)
    simpa only [NestedPeerRelease.cookie_lifted,NestedPeerRelease.cookie_native] using
      NestedPeerRelease.cookie_projects old?
        (NestedPeerRelease.observedOps_projects Event.stagedDisposal stagedDisposal? old? (fun _=>rfl)) msg
  intro mac
  apply HandshakeEffects.scopeOps_projects old? Event.scope CausalSources.Cause.handshake (fun _=>rfl)
  apply ExchangeJoint.receive_ignored old? Event.exchange (fun _=>rfl)
  have base:=ProtocolSender.receive_projects old? (Event.old ∘ TransmitSecurity.Journal.Event.handshake) handshake?
    TransmitSecurity.Journal.Event.handshake TransmitSecurity.Journal.handshake? (fun _=>rfl) (fun _=>rfl)
    sg st kg kt hs hk mac Event.protocolSocket scope? Event.cookieSocket (fun _=>rfl) (fun _=>rfl)
  have repayment:=StagedDisposal.Decoration.receive_projects Event.stagedDisposal stagedDisposal?
    old? (fun _=>rfl) base (fun _=>rfl)
  have accepted : HandshakeWorker.OpsProjects old? (CausalJournal.receiveOps sg kg mac)
      (HandshakeWorker.observedOps TransmitSecurity.Journal.Event.handshake TransmitSecurity.Journal.handshake? st kt mac) :=
    {repayment with
      initiation := fun msg => NestedPeerRelease.initiation_focused_old
        Event.stagedDisposal stagedDisposal? old? (fun _=>rfl) _
        TransmitSecurity.Journal.Event.handshake TransmitSecurity.Journal.handshake? (fun _=>rfl) {mac with input := msg}
      response := fun msg => NestedPeerRelease.response_focused_old
        Event.stagedDisposal stagedDisposal? old? (fun _=>rfl) _
        TransmitSecurity.Journal.Event.handshake TransmitSecurity.Journal.handshake? (fun _=>rfl) {mac with input := msg}}
  have projected:=HandshakeEffects.withEffects_projects old? (Event.old ∘ TransmitSecurity.Journal.Event.handshake)
    TransmitSecurity.Journal.Event.handshake (fun _=>rfl) _ _ effects TimerEffects.lifted accepted effects_projects
  rwa [HandshakeEffects.withEffects_neutral] at projected

private theorem receiver_native (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receiver hooks.session (Driver.keepaliveObserved hooks) msg src)
      (receiveHandshakePacket msg src) := by
  have first:=receiver_old hooks.session TransmitSecurity.Journal.hooks.session
    (Driver.keepaliveObserved hooks) (Driver.keepaliveObserved TransmitSecurity.Journal.hooks)
    hooks_projects.session (Driver.keepalive_projects hooks_projects) msg src
  have second:=HandshakeWorker.observedReceive_projects TransmitSecurity.Journal.Event.handshake
    TransmitSecurity.Journal.handshake? TransmitSecurity.Journal.nonce? (fun _=>rfl)
    TransmitSecurity.Journal.hooks.session Driver.nonceHooks.session
    (Driver.keepaliveObserved TransmitSecurity.Journal.hooks) (Driver.keepaliveObserved Driver.nonceHooks)
    TransmitSecurity.Journal.hooks_projects.session
    (Driver.keepalive_projects TransmitSecurity.Journal.hooks_projects) msg src
  rw [Driver.nonce_keepaliveObserved_eq] at second
  change StateProjectsPrefix TransmitSecurity.Journal.nonce? id _ (receptionWith Nonce.Handshake.ops msg src) at second
  have projected:=Projection.state first second
  have native : ErasesStatePrefix (receptionWith Nonce.Handshake.ops msg src) (receiveHandshakePacket msg src) := by
    rw [←reception_original]
    exact (pinned_const _private.Leanux.Proofs.WG.TransmitSecurity.NonceHandshake.«0».Leanux.Proofs.WG.TransmitSecurity.Nonce.Handshake.reception_erases) msg src
  intro w a h
  have result:=congrArg Prod.fst (projected w a h)
  change (runWGPrefix (receptionWith Nonce.Handshake.ops msg src) w a (h.filterMap (fun e=>(old? e).bind TransmitSecurity.Journal.nonce?))).1 = _ at result
  have reverse : (runWGPrefix (receiver hooks.session (Driver.keepaliveObserved hooks) msg src) w a h).1 =
      (runWGPrefix (receptionWith Nonce.Handshake.ops msg src) w a (h.filterMap (fun e=>(old? e).bind TransmitSecurity.Journal.nonce?))).1 := by
    have mapped:=result.symm
    change Except.map id (runWGPrefix (receiver hooks.session (Driver.keepaliveObserved hooks) msg src) w a h).1 = _ at mapped
    rw [Except.map_id] at mapped
    exact mapped
  exact reverse.trans (native w a _)

private theorem receive_checked (msg : Key) (src : SkbSource) :
    StatePrefixEnsures (fun h w a=>StateInv HeaderLength.Valid Safe h w a ∧ HeaderLength.Valid msg) Safe
      (receiver hooks.session (Driver.keepaliveObserved hooks) msg src)
      (fun _=>StateInv HeaderLength.Valid Safe) := by
  intro w a h before
  apply Journal.checked_state
    (receive_nested hooks.session (Driver.keepaliveObserved hooks) session keepalive msg src before.2)
    (fun w a h result v b valid run=>
      (hoare_iff_run_ambient _ _ _).mp (frame (receiveHandshakePacket_cell msg src)) w a result v b valid
        ((receiver_native msg src w a h).symm.trans run)) w a h before.1

/-- The final source handshake worker obtains its cookie input-size premise
from the actual occupied slot, not an incoming datagram-shape assumption. -/
theorem handshake : Journal.StateSafe HeaderLength.Valid Safe (Driver.handshakeObserved hooks) :=
  worker HeaderLength.Valid Safe _ receive_checked

theorem contracts : Journal.Contracts HeaderLength.Valid Safe hooks old? where
  quiet := quiet_hooks.actors
  projects := hooks_projects
  handshake := handshake

/-- Every cookie socket observation in the initialized final Driver retains
header validation of its own input, including observations before a later Stop. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 :=
  Journal.initialized contracts Safe.empty trace placeholders

/-- An actual cookie reply retains header validation of its own input from
initialized execution; a later Stop does not discard that validation. -/
theorem initialized_cookie (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : CookieSocket.Receipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2=
      pre++Event.cookieSocket receipt::post) : HeaderLength.Valid receipt.input :=
  initialized trace placeholders pre (.cookieSocket receipt) post position

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
