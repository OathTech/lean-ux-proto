import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
import Leanux.Proofs.WG.TransmitSecurity.ReservationStaging

/-! Native allocation receipts retain checked reservations through the initialized
shared driver. Complete staging discharges its source relationship; unrelated
actors can only append events outside the allocation family. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open Driver AuthenticatedEffects Origins.HandshakeSources Journal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem product_quiet {g : PrefixM Journal.Event α} (app : Appends g)
    (frame : HistoryFrame allocation? g) : ProductHistorySafe Safe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have excluded : suffix.filterMap allocation? = [] := by
    have same := frame w h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap allocation? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix g w h).2 := by rw [eq]; exact hi.quiet_suffix excluded
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

private theorem state_quiet {g : WGPrefix Journal.Event α} (app : StateAppends g)
    (frame : StateHistoryFrame allocation? g) : StateHistorySafe Safe g := by
  exact (ReservationHistory.quiet (P := fun _ => True) app frame
    (fun _ _ _ _ => trivial)).consequence
      (fun _ _ _ hi => ⟨hi,trivial⟩) (fun _ _ _ _ hi => hi.1)

private theorem product_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, allocation? (encode e) = none) (g : PrefixM F α) :
    ProductHistorySafe Safe (focusPrefix encode decode g) :=
  product_quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ quiet _)

private theorem state_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, allocation? (encode e) = none) (g : WGPrefix F α) :
    StateHistorySafe Safe (focusStatePrefix encode decode g) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ _ quiet (g.run w))

private theorem emit (e : Journal.Event) (quiet : allocation? e = none) :
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
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ allocation? (fun _ => rfl) _) (fun _ => rfl))
private theorem encrypt (item : Option (List SkbId)) : ProductHistorySafe Safe (Journal.encrypt item) :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ allocation? (fun _ => rfl) _) (fun _ => rfl))
private theorem transmit (pid : PeerId) : ProductHistorySafe Safe (Journal.transmit pid) :=
  product_focus completionEvent completion? (fun e => by cases e <;> rfl) (Completion.step pid)

private theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    ProductHistorySafe Safe (TimerDispatch.scope Event.timerSelected d j pid t entry (Pure.pure ())) := by
  apply product_quiet (TimerDispatch.scope_appends _ _ _ _ _ _ (Appends.pure _))
  intro w h
  rw [TimerDispatch.scope_run,runPrefix_pure]
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,allocation?,List.append_nil]

theorem hooks_safe : ActorHistorySafe Safe Journal.hooks where
  staging := staging
  handshake := handshake
  sendWorker := History.product_lift _
  prepare := product_focus _ _ (fun _ => rfl) _
  counterCheck := fun _ _ => product_quiet (Appends.lift _).receiptObserved
    (HistoryFrame.receiptObserved (HistoryFrame.lift _ _) (fun _ => rfl))
  timerSelected := timer
  confirmation := confirmation
  session := session
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

/-- Every actual allocation in the initialized journal has bounded packet nonces
and completed native reservations in its strict preceding history. This is
reservation provenance, not uniqueness of later encryption occurrences. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  Driver.initialized_actor_history hooks_safe empty trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.ReservationHistory
