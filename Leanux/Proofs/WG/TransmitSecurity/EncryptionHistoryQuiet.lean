import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory

/-! Exact non-encryption journal frames. This interface changes only an unused
hook when proving source paths which cannot perform a transport encryption. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory.Quiet
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Journal Driver AuthenticatedEffects Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def Stable (past : List (Option Nat × SkbId)) (history : List Journal.Event) : Prop := used history = past

private theorem product_quiet {g : PrefixM Journal.Event α} (app : Appends g)
    (frame : HistoryFrame Journal.encryption? g) : ProductHistorySafe (Stable past) g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have safe : (Stable past) (runPrefix g w h).2 := by unfold Stable used; rw [frame w h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

private theorem state_quiet {g : WGPrefix Journal.Event α} (app : StateAppends g)
    (frame : StateHistoryFrame Journal.encryption? g) : StateHistorySafe (Stable past) g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have safe : (Stable past) (runPrefix (g.run w) a h).2 := by unfold Stable used; rw [frame w a h]; exact hi
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix (g.run w) a h).1 <;> trivial

private theorem product_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, Journal.encryption? (encode e) = none) (g : PrefixM F α) :
    ProductHistorySafe (Stable past) (focusPrefix encode decode g) :=
  product_quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ quiet _)

private theorem state_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, Journal.encryption? (encode e) = none) (g : WGPrefix F α) :
    StateHistorySafe (Stable past) (focusStatePrefix encode decode g) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ _ quiet (g.run w))

private theorem emit (e : Journal.Event) (quiet : Journal.encryption? e = none) :
    StateHistorySafe (Stable past) (emitStatePrefix e) := by
  apply StatePrefixEnsures.emit
  all_goals intro h w a hi
  all_goals simpa only [Stable,used,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
    Option.toList_none,List.nil_append,List.append_nil] using hi

private theorem lower {g : PrefixM Journal.Event α} (safe : ProductHistorySafe (Stable past) g) :
    StateHistorySafe (Stable past) (NativeAdapter.lower g) := by
  intro wg a h hi
  obtain ⟨suffix,eq,hs,_⟩ := safe (NativeAdapter.world wg a) h hi
  refine ⟨suffix,eq,hs,?_⟩
  split <;> trivial

private theorem handshake
    (session : PeerId → WGPrefix Journal.Event Bool) (keepalive : PeerId → WGPrefix Journal.Event Unit)
    (hs : ∀ pid, StateHistorySafe (Stable past) (session pid)) (hk : ∀ pid, StateHistorySafe (Stable past) (keepalive pid)) :
    StateHistorySafe (Stable past) (HandshakeWorker.observed Event.handshake handshake? session keepalive) := by
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

private theorem selection (pid : PeerId) : StateHistorySafe (Stable past) (Journal.selection pid) :=
  state_focus _ _ (fun _ => rfl) _
private theorem confirmation (pid : PeerId) (kid : KeypairId) : StateHistorySafe (Stable past) (Journal.confirmation pid kid) :=
  state_focus _ _ (fun _ => rfl) _
private theorem session (pid : PeerId) : StateHistorySafe (Stable past) (Journal.session pid) :=
  state_focus _ _ (fun _ => rfl) _

private theorem reserve (kid : KeypairId) : StateHistorySafe (Stable past) (Journal.reserve kid) :=
  state_quiet ((StateAppends.focus _ _ _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun w => focusPrefix_other Event.nonce nonce? Journal.encryption? (fun _ => rfl) ((Nonce.reserveObserved kid).run w)) _ (fun _ => rfl))
private theorem allocate (packets : List DataPacket) : StateHistorySafe (Stable past) (Journal.allocate packets) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateHistorySafe (Stable past) (Journal.front family addr packets mtu) :=
  state_quiet ((StateAppends.lift _).receiptWGObserved _)
    (StateHistoryFrame.receiptWGObserved (fun _ => HistoryFrame.lift _ _) _ (fun _ => rfl))
private theorem create (pid : PeerId) (item : List SkbId) : StateHistorySafe (Stable past) (Journal.create pid item) :=
  lower (product_focus _ _ (fun _ => rfl) _)
private theorem poll : ProductHistorySafe (Stable past) Journal.poll :=
  product_quiet (Appends.focus _ _ _).receiptObserved
    (HistoryFrame.receiptObserved (focusPrefix_other _ _ Journal.encryption? (fun _ => rfl) _) (fun _ => rfl))

private theorem transmit (pid : PeerId) : ProductHistorySafe (Stable past) (Journal.transmit pid) :=
  product_focus _ _ (fun e => by cases e <;> rfl) _

private theorem timer (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (entry : WheelEntry) :
    ProductHistorySafe (Stable past) (TimerDispatch.scope Event.timerSelected d j pid t entry (pure 0)) := by
  apply product_quiet (TimerDispatch.scope_appends _ _ _ _ _ _ (Appends.pure _))
  intro w h
  rw [TimerDispatch.scope_run,runPrefix_pure]
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,Journal.encryption?,List.append_nil]

/-- Only the unused encryption field is neutralized for non-encryption source
paths. The actual softirq expression remains definitionally unchanged. -/
def nonencryptHooks : Driver.Hooks Journal.Event := {Journal.hooks with encrypt := fun _ => pure false}

theorem hooks_safe : HooksHistorySafe (Stable past) nonencryptHooks where
  stagedPurge := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  peerRelease := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  deliver := Driver.History.product_lift _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.History.state_lift _
  handshake := handshake
  sendWorker := by
    rw [Driver.sendWorker_lift nonencryptHooks rfl]
    exact History.product_lift _
  flushedSend := fun _ => History.state_lift _
  fixtureEnter := fun _ => History.state_pure _
  fixtureLeave := fun _ => History.state_pure _
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
  encrypt := fun _ => History.product_pure _
  transmit := transmit

theorem softirq_history : ProductHistorySafe (Stable past) (Driver.softirqObserved Journal.hooks) :=
  (show Driver.softirqObserved nonencryptHooks = Driver.softirqObserved Journal.hooks from rfl) ▸
    Driver.softirq_history hooks_safe.actors


end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory.Quiet
