import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection

/-! Socket receipt validity through the initialized shared driver. Other event
families stay in the journal but cannot fabricate a socket receipt. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal.SocketHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open Driver AuthenticatedEffects Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def socket? : Journal.Event → Option Completion.SocketReceipt
  | .socket r => some r
  | _ => none

def Safe (h : List Journal.Event) : Prop := ∀ r ∈ h.filterMap socket?, r.Valid

theorem safe_eq (h : List Journal.Event) : Safe h = Completion.Good (h.filterMap completion?) := by
  have maps : (fun x => (completion? x).bind Completion.socket?) = socket? := by
    funext e
    cases e <;> rfl
  simp only [Safe,Completion.Good,List.filterMap_filterMap,maps]

private theorem product_quiet {g : PrefixM Journal.Event α} (app : Appends g)
    (frame : HistoryFrame socket? g) : ProductHistorySafe Safe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have safe : Safe (runPrefix g w h).2 := by unfold Safe; rw [frame w h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

private theorem state_quiet {g : WGPrefix Journal.Event α} (app : StateAppends g)
    (frame : StateHistoryFrame socket? g) : StateHistorySafe Safe g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have safe : Safe (runPrefix (g.run w) a h).2 := by unfold Safe; rw [frame w a h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix (g.run w) a h).1 <;> trivial

private theorem product_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, socket? (encode e) = none) (g : PrefixM F α) :
    ProductHistorySafe Safe (focusPrefix encode decode g) :=
  product_quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ quiet _)

private theorem state_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, socket? (encode e) = none) (g : WGPrefix F α) :
    StateHistorySafe Safe (focusStatePrefix encode decode g) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ _ quiet (g.run w))

private theorem emit (e : Journal.Event) (quiet : socket? e = none) :
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
    (StateHistoryFrame.receiptWGObserved (fun w => focusPrefix_other Event.nonce nonce? socket? (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
private theorem allocate (packets : List DataPacket) : StateHistorySafe Safe (Journal.allocate packets) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateHistorySafe Safe (Journal.front family addr packets mtu) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem create (pid : PeerId) (item : List SkbId) : StateHistorySafe Safe (Journal.create pid item) :=
  lower (product_focus _ _ (fun _ => rfl) _)
private theorem poll : ProductHistorySafe Safe Journal.poll :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ socket? (fun _ => rfl) _) (fun _ => rfl))
private theorem encrypt (item : Option (List SkbId)) : ProductHistorySafe Safe (Journal.encrypt item) :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ socket? (fun _ => rfl) _) (fun _ => rfl))
private theorem transmit (pid : PeerId) : ProductHistorySafe Safe (Journal.transmit pid) := by
  have base : PrefixEnsures (fun h (_ : World) => Completion.Good h) Completion.Good
      (Completion.step pid) (fun _ h (_ : World) => Completion.Good h) := Completion.step_safe pid
  have safe := PrefixEnsures.focus completionEvent completion? (fun e => by cases e <;> rfl) base
  simpa only [Journal.transmit,ProductHistorySafe,PrefixPreserves,← safe_eq] using safe.preserves

private theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    ProductHistorySafe Safe (TimerDispatch.scope Event.timerSelected d j pid t entry (pure ())) := by
  apply product_quiet (TimerDispatch.scope_appends _ _ _ _ _ _ (Appends.pure _))
  intro w h
  rw [TimerDispatch.scope_run,runPrefix_pure]
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,socket?,List.append_nil]

theorem hooks_safe : HooksHistorySafe Safe Journal.hooks where
  handshake := handshake
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
  selection := selection
  confirmation := confirmation
  session := session
  reserve := reserve
  allocate := allocate
  create := create
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

/-- Every socket receipt in an initialized shared-driver history describes the
actual packet, peer and socket action. Later Stop retains the receipt. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  Driver.initialized_actor_history hooks_safe.actors (by intro r member; cases member) trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.Journal.SocketHistory
