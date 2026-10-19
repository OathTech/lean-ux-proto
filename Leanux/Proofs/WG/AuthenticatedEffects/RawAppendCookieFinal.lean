import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendCookieReceive
import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendFinalProjection

/-! Per-input packet bound on the exact final receiver callback. The helper is
a definitional source cut of the same Driver handshake worker, not another
execution or a count over equal input bytes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

abbrev receiverOps (session : PeerId → WGPrefix CausalJournal.Event Bool)
    (keepalive : PeerId → WGPrefix CausalJournal.Event Unit) (mac : HandshakeMac) :=
  HandshakeEffects.scopeOps CausalJournal.Event.scope CausalSources.Cause.handshake
    (HandshakeSecurity.ExchangeJoint.receiveOps CausalJournal.Event.exchange
      (HandshakeEffects.withEffects
        (CausalJournal.receiveOps session keepalive mac)
        (CausalJournal.Event.old ∘ Journal.Event.handshake) CausalJournal.effects))

def receiver (session : PeerId → WGPrefix CausalJournal.Event Bool)
    (keepalive : PeerId → WGPrefix CausalJournal.Event Unit) (msg : Key) (source : SkbSource) :=
  CookieConsumption.receiveWith (RetirementSecurity.NestedPeerRelease.cookieObserved
    CausalJournal.CallbackFrames.nested CausalJournal.Event.cookieConsumed)
    (receiverOps session keepalive) msg source

theorem receiver_factor (session : PeerId → WGPrefix CausalJournal.Event Bool)
    (keepalive : PeerId → WGPrefix CausalJournal.Event Unit) :
    CausalJournal.handshake session keepalive = HandshakeWorker.workerWith (receiver session keepalive) := rfl

theorem receiver_projects
    (sg : PeerId → WGPrefix CausalJournal.Event Bool) (st : PeerId → WGPrefix RawAppend.Event Bool)
    (kg : PeerId → WGPrefix CausalJournal.Event Unit) (kt : PeerId → WGPrefix RawAppend.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix raw? id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix raw? id (kg pid) (kt pid)) (msg : Key) (source : SkbSource) :
    StateProjectsPrefix raw? id (receiver sg kg msg source)
      (CookieConsumption.receiveWith (fun msg => liftWGPrefix (cookieMessageConsume msg))
        (fun _ => RawAppend.receiveOps st kt) msg source) := by
  apply CookieConsumption.receive_projects raw? _ _ _ _
  · intro input
    exact HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
      (CausalJournal.CallbackFrames.cookie_erases input)
      (CausalJournal.CallbackFrames.cookie_quiet raw? (fun _ => rfl) (fun _ => rfl) input).2
  intro mac
  apply HandshakeEffects.scopeOps_projects raw? CausalJournal.Event.scope CausalSources.Cause.handshake (fun _ => rfl)
  apply HandshakeSecurity.ExchangeJoint.receive_ignored raw? CausalJournal.Event.exchange (fun _ => rfl)
  refine {receive_effects_projects raw? (CausalJournal.Event.old ∘ Journal.Event.handshake)
    CausalJournal.handshake? (fun _ => rfl) CausalJournal.effects effects sg st kg kt hs hk mac
    CausalJournal.Event.protocolSocket CausalJournal.scope? CausalJournal.Event.cookieSocket
    (fun _ => rfl) (fun _ => rfl) with initiation := ?_, response := ?_, put := ?_}
  · intro input
    exact HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
      (CausalJournal.CallbackFrames.initiation_erases {mac with input := input})
      (CausalJournal.CallbackFrames.initiation_quiet raw? (fun _ => rfl) (fun _ => rfl) _).2
  · intro input
    exact HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
      (CausalJournal.CallbackFrames.response_erases {mac with input := input})
      (CausalJournal.CallbackFrames.response_quiet raw? (fun _ => rfl) (fun _ => rfl) _).2
  · intro peer
    exact HandshakeSecurity.StagedDisposal.Decoration.release_projects CausalJournal.Event.stagedDisposal
      CausalJournal.stagedDisposal? raw? (fun _ => rfl) peer

/-- The actual final receiver emits at most one original datagram per
qualifying input occurrence. This all-entry source claim needs no initialized
state, callback safety, successful return or matching-by-input-value premise. -/
theorem qualifying_receiver_count (msg : Key) (source : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List CausalJournal.Event)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (qualified : Cookies.FailedMac2 msg source w a) :
    ∃ suffix,
      (runWGPrefix (receiver CausalJournal.hooks.session
        (Driver.keepaliveObserved CausalJournal.hooks) msg source) w a history).2.filterMap raw? =
          history.filterMap raw? ++ suffix ∧ suffix.length ≤ 1 := by
  have projected := congrArg Prod.snd (receiver_projects _ _ _ _ session
    (Driver.keepalive_projects hooks_projects) msg source w a history)
  obtain ⟨suffix,grown,bound⟩ := qualifying_receive_count RawAppend.hooks.session
    (Driver.keepaliveObserved RawAppend.hooks) msg source w a (history.filterMap raw?) kind qualified
  exact ⟨suffix,projected.symm.trans grown,bound⟩

/-- Count on the actual final receiver under its own successful load/MAC
prefix. The count concerns raw native appends, not completed socket returns. -/
theorem checked_receiver_count (msg : Key) (source : SkbSource)
    (w loaded checked : WGWorld) (a b c : Ambient) (history : List CausalJournal.Event)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨ messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (loadRun : (Cookies.loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((true,loaded),b))
    (macRun : ((cookieValidatePacket msg source true).run loaded).run b = .ok ((.noCookie,checked),c)) :
    ∃ suffix,
      (runWGPrefix (receiver CausalJournal.hooks.session
        (TransmitSecurity.Driver.keepaliveObserved CausalJournal.hooks) msg source) w a history).2.filterMap raw? =
        history.filterMap raw? ++ suffix ∧ suffix.length ≤ 1 := by
  have projected := congrArg Prod.snd (receiver_projects CausalJournal.hooks.session RawAppend.hooks.session
    (TransmitSecurity.Driver.keepaliveObserved CausalJournal.hooks)
    (TransmitSecurity.Driver.keepaliveObserved RawAppend.hooks)
    session (TransmitSecurity.Driver.keepalive_projects hooks_projects) msg source w a history)
  obtain ⟨suffix,grown,bound⟩ := RawAppend.checked_receive_count RawAppend.hooks.session
    (TransmitSecurity.Driver.keepaliveObserved RawAppend.hooks) msg source w loaded checked a b c
    (history.filterMap raw?) kind loadRun macRun
  exact ⟨suffix,projected.symm.trans grown,bound⟩

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
