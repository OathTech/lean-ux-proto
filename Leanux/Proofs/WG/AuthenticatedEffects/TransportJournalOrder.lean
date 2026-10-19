import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalHandshake
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderDriver

/-! Confirmation ordering on the same full journal as RX authentication.
Only the actual accepted poll path can emit a confirmation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal.Order
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues TransmitSecurity TransportCarrier Journal
open HandshakeSecurity
open ConfirmationTransportOrder
open Origins.HandshakeSources
set_option maxHeartbeats 600000

abbrev Good := ConfirmationTransportOrder.Safe Event.replay responder?

private theorem other {F : Type} (encode : F → Event)
    (quiet : ∀ e, responder? (encode e) = none) (e : F) : Unconfirmed responder? (encode e) := by
  intro pid kid run found
  rw [quiet] at found
  cases found

private theorem focus_state {F : Type} (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ e, responder? (encode e) = none) (g : WGPrefix F α) :
    Driver.StateHistorySafe Good (focusStatePrefix encode decode g) :=
  ConfirmationTransportOrder.focus_state Event.replay responder? encode decode (other encode quiet) g

private theorem focus_product {F : Type} (encode : F → Event) (decode : Event → Option F)
    (quiet : ∀ e, responder? (encode e) = none) (g : PrefixM F α) :
    Driver.ProductHistorySafe Good (focusPrefix encode decode g) :=
  ConfirmationTransportOrder.focus_product Event.replay responder? encode decode (other encode quiet) g

private theorem receipt_state (g : WGPrefix Event α) (make : WGRunWitness α → Event)
    (quiet : ∀ r, responder? (make r) = none) (safe : Driver.StateHistorySafe Good g) :
    Driver.StateHistorySafe Good (receiptWGObserved g make) :=
  ConfirmationTransportOrder.receipt_state Event.replay responder? g make (other make quiet) safe

private theorem receipt_product (g : PrefixM Event α) (make : RunWitness α → Event)
    (quiet : ∀ r, responder? (make r) = none) (safe : Driver.ProductHistorySafe Good g) :
    Driver.ProductHistorySafe Good (receiptObserved g make) :=
  ConfirmationTransportOrder.receipt_product Event.replay responder? g make (other make quiet) safe

private theorem emit (event : Event) (quiet : responder? event = none) :
    Driver.StateHistorySafe Good (emitStatePrefix event) := by
  apply StatePrefixEnsures.emit
  all_goals intro h w a hi
  all_goals exact hi.quiet (by
    intro e member
    have eq : e = event := List.mem_singleton.mp member
    subst e
    exact other (fun _ : Unit => event) (fun _ => quiet) ())

private theorem handshake
    (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Driver.StateHistorySafe Good (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe Good (keepalive pid)) :
    Driver.StateHistorySafe Good (HandshakeWorker.observed Event.handshake handshake? session keepalive) := by
  unfold HandshakeWorker.observed HandshakeWorker.workerWith HandshakeWorker.observedReceive
    afterMacWith responseWith
  simp only [HandshakeWorker.observedOps,HandshakeWorker.callback]
  repeat' first
    | with_reducible exact hs _
    | with_reducible exact hk _
    | (driver_history_head HandshakeWorker.old; exact focus_state _ _ (fun _ => rfl) _)
    | (driver_history_head emitStatePrefix; exact emit _ rfl)
    | (driver_history_head captureWGRun
       exact StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi))
    | driver_state_history_step

private theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    Driver.ProductHistorySafe Good (Journal.hooks.timerSelected d j pid t entry) := by
  intro w h hi
  dsimp only [Journal.hooks]
  rw [TimerDispatch.scope_run,runPrefix_pure]
  let event := Event.timerSelected ⟨d,j,pid,t,entry,w⟩
  have safe : Good (h ++ [event]) := hi.quiet (by
    intro e member
    have eq : e = event := List.mem_singleton.mp member
    subst e
    exact other (fun _ : Unit => event) (fun _ => rfl) ())
  exact ⟨[event],rfl,safe,safe⟩

theorem quiet : QuietHooksSafe Good Journal.hooks where
  deliver := Driver.History.product_lift _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.History.state_lift _
  fixtureEnter := fun _ => Driver.History.state_pure _
  fixtureLeave := fun _ => Driver.History.state_pure _
  stagedPurge := fun _ => Driver.History.state_lift _
  peerRelease := fun _ => Driver.History.state_lift _
  armTimer := fun _ _ _ _ => Driver.History.state_lift _
  queueSend := fun _ => Driver.History.state_lift _
  handshake := handshake
  sendWorker := by
    rw [Driver.sendWorker_lift Journal.hooks rfl]
    exact Driver.History.product_lift _
  flushedSend := fun _ => Driver.History.state_lift _
  candidateEnter := fun _ _ => Driver.History.product_pure _
  candidateLeave := fun _ => Driver.History.product_pure _
  stackInput := fun _ _ preserves => preserves
  prepare := focus_product _ _ (fun _ => rfl) _
  counterCheck := fun _ _ => receipt_product _ _ (fun _ => rfl) (Driver.History.product_lift _)
  timerSelected := timer
  timerFinished := fun _ => Driver.History.product_pure _
  selection := ConfirmationTransportOrder.selection Event.replay Event.responder responder? (fun _ => rfl)
  session := ConfirmationTransportOrder.session Event.replay Event.responder responder? (fun _ => rfl)
  reserve := fun _ => receipt_state _ _ (fun _ => rfl) (focus_state _ _ (fun _ => rfl) _)
  allocate := fun _ => receipt_state _ _ (fun _ => rfl) (Driver.History.state_lift _)
  create := fun _ _ => ConfirmationTransportOrder.lower Event.replay responder? _ (focus_product _ _ (fun _ => rfl) _)
  front := fun _ _ _ _ => receipt_state _ _ (fun _ => rfl) (Driver.History.state_lift _)
  poll := receipt_product _ _ (fun _ => rfl) (focus_product _ _ (fun _ => rfl) _)
  encrypt := fun _ => receipt_product _ _ (fun _ => rfl) (focus_product _ _ (fun _ => rfl) _)
  transmit := fun _ => focus_product completionEvent completion? (fun e => by cases e <;> rfl) _

theorem nativePoll (pid : PeerId) (budget : Nat) :
    Driver.ProductHistorySafe Good (Driver.nativePollObserved Journal.hooks pid budget) :=
  quiet_nativePoll Event.replay Event.responder responder? (fun _ => rfl)
    (other Event.replay (fun _ => rfl)) quiet rfl rfl pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal.Order
