import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection

/-! Routing-admission receipts on the initialized shared driver. The front ends at
the actual staged splice, before a potentially stopped send tail. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal.RoutingHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Driver AuthenticatedEffects Origins.HandshakeSources Packets
set_option maxHeartbeats 600000
set_option pp.structureInstances false

structure Receipt where
  family : Nat
  addr : Nat
  packets : List Packet
  mtu : Nat
  run : WGRunWitness (Except Int PeerId)

def Receipt.Valid (r : Receipt) : Prop :=
  r.run.Valid (Packets.txFront r.family r.addr r.packets r.mtu)

def routed? : Journal.Event → Option Receipt
  | .routed family addr packets mtu run => some ⟨family,addr,packets,mtu,run⟩
  | _ => none

def Safe (h : List Journal.Event) : Prop := ∀ r ∈ h.filterMap routed?, r.Valid

private theorem product_quiet {g : PrefixM Journal.Event α} (app : Appends g)
    (frame : HistoryFrame routed? g) : ProductHistorySafe Safe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have safe : Safe (runPrefix g w h).2 := by unfold Safe; rw [frame w h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

private theorem state_quiet {g : WGPrefix Journal.Event α} (app : StateAppends g)
    (frame : StateHistoryFrame routed? g) : StateHistorySafe Safe g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have safe : Safe (runPrefix (g.run w) a h).2 := by unfold Safe; rw [frame w a h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix (g.run w) a h).1 <;> trivial

private theorem product_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, routed? (encode e) = none) (g : PrefixM F α) :
    ProductHistorySafe Safe (focusPrefix encode decode g) :=
  product_quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ quiet _)

private theorem state_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, routed? (encode e) = none) (g : WGPrefix F α) :
    StateHistorySafe Safe (focusStatePrefix encode decode g) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ _ quiet (g.run w))

private theorem emit (e : Journal.Event) (quiet : routed? e = none) :
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
    (StateHistoryFrame.receiptWGObserved (fun w => focusPrefix_other Event.nonce nonce? routed? (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
private theorem allocate (packets : List DataPacket) : StateHistorySafe Safe (Journal.allocate packets) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateHistorySafe Safe (Journal.front family addr packets mtu) := by
  intro w a h hi
  have observed := runWGPrefix_receiptWGObserved (liftWGPrefix (txFront family addr packets mtu))
    (Journal.Event.routed family addr packets mtu) w a h
  rw [runWGPrefix_lift] at observed
  simp only [runWGPrefix,runStatePrefix] at observed
  unfold Journal.front
  rw [observed]
  cases run : ((Packets.txFront family addr packets mtu).run w).run a with
  | error stop => exact ⟨[],by simp,hi,True.intro⟩
  | ok output =>
    obtain ⟨⟨value,v⟩,b⟩ := output
    have good : Safe (h ++ [.routed family addr packets mtu ⟨value,w,v,a,b⟩]) := by
      intro receipt member
      simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,routed?,
        List.mem_append,List.mem_singleton] at member
      rcases member with old | rfl
      · exact hi receipt old
      · exact run
    exact ⟨[.routed family addr packets mtu ⟨value,w,v,a,b⟩],rfl,good,good⟩
private theorem create (pid : PeerId) (item : List SkbId) : StateHistorySafe Safe (Journal.create pid item) :=
  lower (product_focus _ _ (fun _ => rfl) _)
private theorem poll : ProductHistorySafe Safe Journal.poll :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ routed? (fun _ => rfl) _) (fun _ => rfl))
private theorem encrypt (item : Option (List SkbId)) : ProductHistorySafe Safe (Journal.encrypt item) :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ routed? (fun _ => rfl) _) (fun _ => rfl))
private theorem transmit (pid : PeerId) : ProductHistorySafe Safe (Journal.transmit pid) :=
  product_focus _ _ (fun event => by cases event <;> rfl) _

private theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    ProductHistorySafe Safe (TimerDispatch.scope Event.timerSelected d j pid t entry (pure 0)) := by
  apply product_quiet (TimerDispatch.scope_appends _ _ _ _ _ _ (Appends.pure _))
  intro w h
  rw [TimerDispatch.scope_run,runPrefix_pure]
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,routed?,List.append_nil]

theorem hooks_safe : HooksHistorySafe Safe Journal.hooks where
  keepalivePrepare := fun _ => TransmitSecurity.Driver.History.state_lift _
  fixtureEnter := fun _ => History.state_pure _
  fixtureLeave := fun _ => History.state_pure _
  handshake := handshake
  sendWorker := by
    rw [Driver.sendWorker_lift _ rfl]
    exact History.product_lift _
  flushedSend := fun _ => History.state_lift _
  armTimer := fun _ _ _ _ => History.state_lift _
  queueSend := fun _ => History.state_lift _
  candidateEnter := fun _ _ => History.product_pure _
  candidateLeave := fun _ => History.product_pure _
  stackInput := fun _ _ preserves => preserves
  prepare := product_focus _ _ (fun _ => rfl) _
  counterCheck := fun _ _ => product_quiet (Appends.lift _).receiptObserved
    (HistoryFrame.receiptObserved (HistoryFrame.lift _ _) (fun _ => rfl))
  timerSelected := timer
  timerFinished := fun _ => History.product_pure _
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

/-- Every actual routing admission retains its connected native front execution,
including admissions before a later Stop. -/
theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  Driver.initialized_actor_history hooks_safe.actors (by intro r member; cases member) trace placeholders

/-- A successful receipt contains the original destination lookup and the
completed splice; a later send failure does not erase this admission. -/
theorem Receipt.selection (receipt : Receipt) (valid : receipt.Valid)
    (pid : PeerId) (selected : receipt.run.value = .ok pid) :
    TxFrontCut receipt.family receipt.addr receipt.packets receipt.mtu
      receipt.run.before receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter pid ∧
    ∀ packet ∈ receipt.packets, destinationField receipt.family packet.bytes = receipt.addr := by
  have native := valid
  change ((txFront receipt.family receipt.addr receipt.packets receipt.mtu).run
    receipt.run.before).run receipt.run.ambientBefore =
      .ok ((receipt.run.value,receipt.run.after),receipt.run.ambientAfter) at native
  rw [selected] at native
  have cut := txFront_cut _ _ _ _ _ _ _ _ _ native
  refine ⟨cut,?_⟩
  obtain ⟨u,_,_,a,_,_,checked,_,_,_⟩ := cut
  exact ((hoare_iff_run_ambient _ _ _).mp
    (txCheck_valid receipt.family receipt.addr receipt.packets receipt.mtu)
      _ _ true u a True.intro checked rfl).2

/-- R3's existing native authorization contract is reused at this actual front;
its flat routing relation remains explicit in this local statement. -/
theorem Receipt.authorized (receipt : Receipt) (valid : receipt.Valid)
    (v4 : Bool) (family : receipt.family = if v4 then 4 else 6)
    (pid : PeerId) (selected : receipt.run.value = .ok pid)
    (table : AllowedIps.FlatTable × AllowedIps.FlatTable)
    (routing : AllowedIps.RoutedView (AllowedIps.routingView receipt.run.before) table) :
    AllowedIps.PeerWinner (AllowedIps.rootWidth v4) receipt.addr
      (AllowedIps.selectedFlat v4 table) (some pid) := by
  have native := valid
  change ((txFront receipt.family receipt.addr receipt.packets receipt.mtu).run
    receipt.run.before).run receipt.run.ambientBefore =
      .ok ((receipt.run.value,receipt.run.after),receipt.run.ambientAfter) at native
  rw [family,selected] at native
  exact (txFront_authorized v4 _ _ _ _ _ _ _ pid table routing native).2.1

end Leanux.Proofs.WG.TransmitSecurity.Journal.RoutingHistory
