import Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter

/-! Non-poll source paths preserve actual poll certificates. Softirq's source
never calls the encryption poll hook; its exact existing driver term is kept. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Journal Driver AuthenticatedEffects Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem product_quiet {g : PrefixM Journal.Event α} (app : Appends g)
    (frame : HistoryFrame polled? g) : ProductHistorySafe Safe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have safe : Safe (runPrefix g w h).2 := by unfold Safe; rw [frame w h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

private theorem state_quiet {g : WGPrefix Journal.Event α} (app : StateAppends g)
    (frame : StateHistoryFrame polled? g) : StateHistorySafe Safe g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have safe : Safe (runPrefix (g.run w) a h).2 := by unfold Safe; rw [frame w a h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix (g.run w) a h).1 <;> trivial

private theorem product_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, polled? (encode e) = none) (g : PrefixM F α) :
    ProductHistorySafe Safe (focusPrefix encode decode g) :=
  product_quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ quiet _)

private theorem state_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, polled? (encode e) = none) (g : WGPrefix F α) :
    StateHistorySafe Safe (focusStatePrefix encode decode g) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ _ quiet (g.run w))

private theorem emit (e : Journal.Event) (quiet : polled? e = none) :
    StateHistorySafe Safe (emitStatePrefix e) := by
  apply StatePrefixEnsures.emit
  all_goals intro h w a hi
  all_goals simpa only [Safe,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
    Option.toList_none,List.nil_append,List.append_nil] using hi

private theorem lower {g : PrefixM Journal.Event α} (safe : ProductHistorySafe Safe g) :
    StateHistorySafe Safe (NativeAdapter.lower g) := by
  intro wg a h hi
  obtain ⟨suffix,eq,hs,_⟩ := safe (NativeAdapter.world wg a) h hi
  refine ⟨suffix,eq,hs,?_⟩
  split <;> trivial

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

private theorem selection (pid : PeerId) : StateHistorySafe Safe (Journal.selection pid) :=
  state_focus _ _ (fun _ => rfl) _
private theorem confirmation (pid : PeerId) (kid : KeypairId) : StateHistorySafe Safe (Journal.confirmation pid kid) :=
  state_focus _ _ (fun _ => rfl) _
private theorem session (pid : PeerId) : StateHistorySafe Safe (Journal.session pid) :=
  state_focus _ _ (fun _ => rfl) _

private theorem reserve (kid : KeypairId) : StateHistorySafe Safe (Journal.reserve kid) :=
  state_quiet ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun w => focusPrefix_other Event.nonce nonce? polled? (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
private theorem allocate (packets : List DataPacket) : StateHistorySafe Safe (Journal.allocate packets) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateHistorySafe Safe (Journal.front family addr packets mtu) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem create (pid : PeerId) (item : List SkbId) : StateHistorySafe Safe (Journal.create pid item) :=
  lower (product_focus _ _ (fun _ => rfl) _)
private theorem encrypt (item : Option (List SkbId)) : ProductHistorySafe Safe (Journal.encrypt item) :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ polled? (fun _ => rfl) _) (fun _ => rfl))
private theorem transmit (pid : PeerId) : ProductHistorySafe Safe (Journal.transmit pid) :=
  product_focus _ _ (fun e => by cases e <;> rfl) _

private theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    ProductHistorySafe Safe (TimerDispatch.scope Event.timerSelected d j pid t entry (pure ())) := by
  apply product_quiet (TimerDispatch.scope_appends _ _ _ _ _ _ (Appends.pure _))
  intro w h
  rw [TimerDispatch.scope_run,runPrefix_pure]
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,polled?,List.append_nil]

/-- Only the unused poll field is neutralized to apply the existing history
interface. The actual softirq expression is definitionally unchanged. -/
def nonpollHooks : Driver.Hooks Journal.Event := {Journal.hooks with poll := pure none}

theorem hooks_safe : HooksHistorySafe Safe nonpollHooks where
  handshake := handshake
  sendWorker := by
    rw [Driver.sendWorker_lift nonpollHooks rfl]
    exact History.product_lift _
  flushedSend := fun _ => History.state_lift _
  candidateEnter := fun _ _ => History.product_pure _
  candidateLeave := fun _ => History.product_pure _
  prepare := product_focus _ _ (fun _ => rfl) _
  counterCheck := fun _ _ => product_quiet (Appends.lift _).receiptObserved
    (HistoryFrame.receiptObserved (HistoryFrame.lift _ _) (fun _ => rfl))
  timerSelected := timer
  selection := selection
  confirmation := confirmation
  session := session
  reserve := reserve
  allocate := allocate
  create := create
  front := front
  poll := History.product_pure _
  encrypt := encrypt
  transmit := transmit

theorem softirq_history : ProductHistorySafe Safe (Driver.softirqObserved Journal.hooks) :=
  (show Driver.softirqObserved nonpollHooks = Driver.softirqObserved Journal.hooks from rfl) ▸
    Driver.softirq_history hooks_safe.actors

theorem softirq : PrefixPreserves (Inv active) Safe (Driver.softirqObserved Journal.hooks) := by
  intro w h before
  obtain ⟨suffix,extension,safe,normal⟩ := softirq_history w h before.2
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (Driver.softirqObserved Journal.hooks) w h).1 with
  | error stop => trivial
  | ok output =>
    obtain ⟨value,v⟩ := output
    cases value
    exact ⟨OccurrenceDriverCuts.softirq Journal.hooks_projects before.1 h result,safe⟩

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
