import Leanux.Proofs.WG.HandshakeSecurity.ReservationSelectionStaging
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection

/-! The actual staging source discharges reservation-to-selection chronology.
The shared driver retains this positional property through every native actor. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity Driver AuthenticatedEffects Origins.HandshakeSources Journal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem emit (e : Journal.Event) (quiet : reservation? e = none) :
    StateHistorySafe Safe (emitStatePrefix e) := by
  apply StatePrefixEnsures.emit
  all_goals intro h w a hi
  all_goals exact hi.quiet quiet

private theorem handshake
    (session : PeerId → WGPrefix Journal.Event Bool) (keepalive : PeerId → WGPrefix Journal.Event Unit)
    (hs : ∀ pid, StateHistorySafe Safe (session pid)) (hk : ∀ pid, StateHistorySafe Safe (keepalive pid)) :
    StateHistorySafe Safe (HandshakeWorker.observed Event.handshake handshake? session keepalive) := by
  unfold HandshakeWorker.observed HandshakeWorker.workerWith HandshakeWorker.observedReceive
    afterMacWith responseWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' first
    | with_reducible exact hs _
    | with_reducible exact hk _
    | (driver_history_head HandshakeWorker.old; exact state_focus _ _ (fun _ => rfl) _)
    | (driver_history_head emitStatePrefix; exact emit _ rfl)
    | (driver_history_head captureWGRun
       exact StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi))
    | driver_state_history_step

private theorem confirmation (pid : PeerId) (kid : KeypairId) : StateHistorySafe Safe (Journal.confirmation pid kid) :=
  state_focus _ _ (fun _ => rfl) _
private theorem session (pid : PeerId) : StateHistorySafe Safe (Journal.session pid) :=
  state_focus _ _ (fun _ => rfl) _

private theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateHistorySafe Safe (Journal.front family addr packets mtu) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem poll : ProductHistorySafe Safe Journal.poll :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ reservation? (fun _ => rfl) _) (fun _ => rfl))
private theorem encrypt (item : Option (List SkbId)) : ProductHistorySafe Safe (Journal.encrypt item) :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ reservation? (fun _ => rfl) _) (fun _ => rfl))
private theorem transmit (pid : PeerId) : ProductHistorySafe Safe (Journal.transmit pid) :=
  product_focus completionEvent completion? (fun e => by cases e <;> rfl) (Completion.step pid)

private theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    ProductHistorySafe Safe (TimerDispatch.scope Event.timerSelected d j pid t entry (Pure.pure 0)) := by
  apply product_quiet (TimerDispatch.scope_appends _ _ _ _ _ _ (Appends.pure _))
  intro w h
  rw [TimerDispatch.scope_run,runPrefix_pure]
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,reservation?,List.append_nil]

theorem hooks_core : ActorCoreHistorySafe Safe Journal.hooks where
  deliver := Driver.History.product_lift _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.History.state_lift _
  staging := staging
  fixtureEnter := fun _ => History.state_pure _
  fixtureLeave := fun _ => History.state_pure _
  handshake := handshake _ _ session (keepalive_staging_history (fun _ => History.state_lift _) staging)
  sendWorker := by
    rw [Driver.sendWorker_lift _ rfl]
    exact History.product_lift _
  flushedSend := fun _ => History.state_lift _
  armTimer := fun _ _ _ _ => History.state_lift _
  queueSend := fun _ => History.state_lift _
  candidateEnter := fun _ _ => History.product_pure _
  candidateLeave := fun _ => History.product_pure _
  prepare := product_focus _ _ (fun _ => rfl) _
  counterCheck := fun _ _ => product_quiet (Appends.lift _).receiptObserved
    (HistoryFrame.receiptObserved (HistoryFrame.lift _ _) (fun _ => rfl))
  timerSelected := timer
  timerFinished := fun _ => History.product_pure _
  confirmation := confirmation
  session := session
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

theorem hooks_safe : ActorHistorySafe Safe Journal.hooks :=
  hooks_core.withPoll (fun _ _ preserves => preserves)


/-- Every initialized native reservation uses the same key core as an actual
earlier current-slot selection in this journal. No incoming carrier remains. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  Driver.initialized_actor_history hooks_safe empty trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
