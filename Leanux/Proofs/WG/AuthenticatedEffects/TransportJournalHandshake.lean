import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalWorkers
import Leanux.Proofs.WG.AuthenticatedEffects.TransportHandshakeFrames

/-! Actual handshake callbacks preserve transport authentication carriers even
when a later callback stops. Handshake events stay in the same journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransportCarrier Journal Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem call (kind : HandshakeCausal.Kind) (pid : PeerId) (action : WG.M α)
    (frame : SameView RxDisposition.nativeRxStore action) :
    StateSafe (HandshakeWorker.old Event.handshake handshake? (HandshakeCausal.call kind pid action)) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun _ => focusPrefix_other Event.handshake handshake? replay? (fun _ => rfl) _)
    (focusStatePrefix_erases _ _ (HandshakeCausal.call_erases kind pid action)) frame

private theorem initiation (mac : HandshakeMac) :
    StateSafe (HandshakeWorker.old Event.handshake handshake? (HandshakeCausal.initiation mac)) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun _ => focusPrefix_other Event.handshake handshake? replay? (fun _ => rfl) _)
    (focusStatePrefix_erases _ _ (HandshakeCausal.initiation_erases mac))
    (TransportHandshakeFrames.consumeInitiation mac.input)

private theorem response (mac : HandshakeMac) :
    StateSafe (HandshakeWorker.old Event.handshake handshake? (HandshakeCausal.response mac)) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun _ => focusPrefix_other Event.handshake handshake? replay? (fun _ => rfl) _)
    (focusStatePrefix_erases _ _ (HandshakeCausal.response_erases mac))
    (TransportHandshakeFrames.consumeResponse mac.input)

private theorem emit (e : HandshakeCausal.Event) : StateSafe (emitStatePrefix (Event.handshake e)) :=
  state_quiet (fun _ _ _ => ⟨[Event.handshake e],rfl⟩)
    (fun _ _ h => by
      change (h ++ [Event.handshake e]).filterMap replay? = h.filterMap replay?
      simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,replay?,List.append_nil])
    (erasesStatePrefix_emit _) (SameView.pure _ _)

private theorem capture (action : WG.M α) (frame : SameView RxDisposition.nativeRxStore action) :
    StateSafe (captureWGRun action) := by
  apply StatePrefixEnsures.captureWGRun action (fun _ _ _ hi => hi.2)
  intro h w a x v b hi run
  exact ⟨hi.1.sameRx ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a x v b run),hi.2⟩

macro "journal_handshake_rx" : tactic => `(tactic| first
  | (snapshot_head createResponse; exact TransportHandshakeFrames.createResponse _)
  | (snapshot_head addMacToPacket; exact TransportHandshakeFrames.mac _ _)
  | (snapshot_head sendBufferToPeer; exact TransportHandshakeFrames.send _ _)
  | (snapshot_head timersSessionDerived; exact TransportHandshakeFrames.derived _)
  | (snapshot_head timersTraversal; exact TransportHandshakeFrames.traversal _)
  | (snapshot_head timersAnyAuthenticatedPacketSent; exact TransportHandshakeFrames.sent _)
  | (snapshot_head timersAnyAuthenticatedPacketReceived; exact TransportHandshakeFrames.received _)
  | (snapshot_head timersHandshakeComplete; exact handshakeComplete_rx _ _)
  | (snapshot_head setPeerEndpointFromSkb; exact TransportHandshakeFrames.endpoint _ _)
  | (snapshot_head cookieMessageConsume; exact TransportHandshakeFrames.cookieConsume _)
  | (snapshot_head sendHandshakeCookie; exact TransportHandshakeFrames.sendCookie _ _)
  | (snapshot_head Cookies.loadPhase; exact TransportPublication.store_rx _ Cookies.loadPhase_sameStore)
  | (snapshot_head cookieValidatePacket; exact TransportHandshakeFrames.cookie _ (cookieValidatePacket_sameCookie _ _ _))
  | (snapshot_head modifyDev; apply modifyDev_rx <;> intro d <;> rfl)
  | (snapshot_head hiddenClock64; unfold hiddenClock64; transport_native_rx)
  | (snapshot_head WG.orM; unfold WG.orM; transport_native_rx)
  | (solve | transport_native_rx))

open Lean Meta Elab Tactic in
elab "transport_carrier_local " callback:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``TransportCarrier.StateSafe do throwError "not a state carrier"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← Elab.Term.elabTerm callback none
  unless action.getAppFn == expected do throwError "different callback"

open Lean Meta Elab Tactic in
elab "journal_old_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``TransportCarrier.StateSafe do throwError "not a state carrier"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``HandshakeWorker.old do throwError "not an old cut"
  let body := action.getAppArgs.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless body.getAppFn.constName? == some expected do throwError "different cut"

macro "journal_handshake_source " session:ident keepalive:ident hs:ident hk:ident : tactic => `(tactic| first
  | (transport_carrier_local $session; exact $hs _)
  | (transport_carrier_local $keepalive; exact $hk _)
  | (journal_old_head HandshakeCausal.initiation; exact initiation _)
  | (journal_old_head HandshakeCausal.response; exact response _)
  | (journal_old_head HandshakeCausal.call; apply call; journal_handshake_rx)
  | (transport_carrier_head emitStatePrefix; exact emit _)
  | (transport_carrier_head captureWGRun; apply capture; journal_handshake_rx)
  | (transport_carrier_head liftWGPrefix; apply state_rx; journal_handshake_rx)
  | transport_carrier_state_step)

private theorem response_with
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (_hk : ∀ pid, StateSafe (keepalive pid))
    (mac : HandshakeMac) (pid : PeerId) :
    StateSafe (responseWith (HandshakeWorker.observedOps Event.handshake handshake? session keepalive mac) pid) := by
  unfold responseWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  change TransportCarrier.StateSafe (fun _ => True) origin? replay? _
  repeat' journal_handshake_source session keepalive hs _hk

private theorem after_with
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid))
    (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    StateSafe (afterMacWith (HandshakeWorker.observedOps Event.handshake handshake? session keepalive mac)
      msg src loaded state) := by
  unfold afterMacWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  change TransportCarrier.StateSafe (fun _ => True) origin? replay? _
  repeat' first
    | (transport_carrier_head responseWith; exact response_with session keepalive hs hk _ _)
    | journal_handshake_source session keepalive hs hk

private theorem receive_with
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid))
    (msg : Key) (src : SkbSource) :
    StateSafe (HandshakeWorker.observedReceive Event.handshake handshake? session keepalive msg src) := by
  unfold HandshakeWorker.observedReceive
  change TransportCarrier.StateSafe (fun _ => True) origin? replay? _
  repeat' first
    | (transport_carrier_head afterMacWith; exact after_with session keepalive hs hk _ _ _ _ _)
    | journal_handshake_source session keepalive hs hk

theorem observed
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, StateSafe (session pid)) (hk : ∀ pid, StateSafe (keepalive pid)) :
    StateSafe (HandshakeWorker.observed Event.handshake handshake? session keepalive) := by
  unfold HandshakeWorker.observed HandshakeWorker.workerWith
  change TransportCarrier.StateSafe (fun _ => True) origin? replay? _
  repeat' first
    | (transport_carrier_head HandshakeWorker.observedReceive; exact receive_with session keepalive hs hk _ _)
    | journal_handshake_source session keepalive hs hk

theorem handshake : StateSafe (Driver.handshakeObserved Journal.hooks) :=
  observed Journal.session (Driver.keepaliveObserved Journal.hooks) session
    (TransportCarrier.keepalive staging)

theorem callbacks : DeferredSafe (fun _ => True) origin? replay? Journal.hooks where
  deliver := product_storeLift _ Leanux.Proofs.Framing.deliverSent_sameKernel
  keepalivePrepare := keepalive_prepare
  fixtureEnter := fun _ => state_pure _
  fixtureLeave := fun _ => state_pure _
  stagedPurge := stagedPurge
  peerRelease := peerRelease
  armTimer := armTimer
  queueSend := queueSend
  selection := selection
  reserve := reserve
  allocate := allocate
  create := create
  prepare := prepare
  poll := poll
  encrypt := encrypt
  transmit := transmit
  handshake := handshake
  napi := nativePoll
  sendWorker := sendWorker
  flushedSend := flushedSend
  selected := timer
  finished := timerFinished

/-- Every actual replay-check receipt from an initialized shared execution
retains its earlier authenticated native publication, including stopped runs. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    TransportReplay.Safe origin? replay? (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  (TransportCarrier.initialized callbacks front True.intro trace placeholders).1

end Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
