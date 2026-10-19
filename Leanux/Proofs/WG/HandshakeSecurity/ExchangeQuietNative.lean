import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryWorkers

/-! Unobserved native side paths preserve the complete exchange journal.
Native erasure alone would not establish that; the independent exact history
frame is also required before identifying these actions with a native lift. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AuthenticatedEffects.TimerEffects
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

theorem native_via_nonce {g : WGPrefix Exchange.Event α} {n : WGPrefix Nonce.Allocation α}
    {empty : WGPrefix Empty α} {action : WG.M α}
    (pg : StateProjectsPrefix NativeDriver.erase id g empty)
    (pn : StateProjectsPrefix NativeDriver.erase id n empty)
    (erases : ErasesStatePrefix n action) : ErasesStatePrefix g action := by
  intro w a h
  have first := congrArg Prod.fst (pg w a h)
  have second := congrArg Prod.fst (pn w a [])
  have identity : (fun x : (α × WGWorld) × Ambient => (Prod.map id id x.1,x.2)) = id := by
    funext x
    rcases x with ⟨⟨value,world⟩,ambient⟩
    rfl
  simp only [NativeDriver.filter_empty,identity,Except.map_id] at first second
  exact first.symm.trans (second.trans (erases w a []))

private theorem frame_lift (action : WG.M α) : StateHistoryFrame some (liftWGPrefix action : WGPrefix Exchange.Event α) := by
  intro w a h
  rfl

macro "exchange_quiet_step " rho:ident : tactic => `(tactic| first
  | with_reducible exact frame_lift _
  | timer_effects_frame_step $rho)

theorem staging_quiet (pid : PeerId) : StateHistoryFrame some (Driver.stagingObserved hooks pid) := by
  unfold Driver.stagingObserved
  simp only [Driver.noKey_lift hooks rfl]
  dsimp only [hooks]
  let rho : Exchange.Event → Option Exchange.Event := some
  change StateHistoryFrame rho _
  repeat' exchange_quiet_step rho

theorem staging_lift (pid : PeerId) :
    Driver.stagingObserved hooks pid = liftWGPrefix (sendStagedPackets pid) := by
  apply eq_native_lift _ (staging_quiet pid)
  apply native_via_nonce (Driver.staging_projects native_projection pid)
    (Driver.staging_projects NativeDriver.nonce_projection pid)
  rw [Driver.nonce_staging_specialization]
  exact Nonce.stagingObserved_erases pid

theorem transmit_lift (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.transmitObserved hooks family addr packets mtu =
      liftWGPrefix (wgXmit family addr packets mtu) := by
  apply eq_native_lift
  · apply native_via_nonce (Driver.transmit_projects native_projection family addr packets mtu)
      (Driver.transmit_projects NativeDriver.nonce_projection family addr packets mtu)
    rw [Driver.nonce_transmitObserved_eq]
    exact Nonce.transmitObserved_erases family addr packets mtu
  · unfold Driver.transmitObserved
    simp only [staging_lift]
    dsimp only [hooks]
    let rho : Exchange.Event → Option Exchange.Event := some
    change StateHistoryFrame rho _
    repeat' exchange_quiet_step rho

theorem keepalive_quiet (pid : PeerId) : StateHistoryFrame some (Driver.keepaliveObserved hooks pid) := by
  rw [Driver.keepalive_native _ rfl]
  unfold Driver.keepaliveInline
  rw [staging_lift]
  let rho : Exchange.Event → Option Exchange.Event := some
  change StateHistoryFrame rho _
  repeat' exchange_quiet_step rho

theorem keepalive_lift (pid : PeerId) :
    Driver.keepaliveObserved hooks pid = liftWGPrefix (sendKeepalive pid) := by
  apply eq_native_lift _ (keepalive_quiet pid)
  apply native_via_nonce (Driver.keepalive_projects native_projection pid)
    (Driver.keepalive_projects NativeDriver.nonce_projection pid)
  rw [Driver.nonce_keepaliveObserved_eq]
  exact Nonce.keepaliveObserved_erases pid

theorem receiveTail_quiet (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateHistoryFrame some (Driver.receiveTailObserved hooks pid pkt confirmed) := by
  unfold Driver.receiveTailObserved
  simp only [Driver.prepare_lift hooks rfl,staging_lift]
  let rho : Exchange.Event → Option Exchange.Event := some
  change StateHistoryFrame rho _
  repeat' exchange_quiet_step rho

theorem consume_quiet (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StateHistoryFrame some (Driver.consumeObserved hooks pid pkt ep) := by
  unfold Driver.consumeObserved
  dsimp only [hooks]
  apply StateHistoryFrame.bind (frame_lift _)
  intro _
  apply StateHistoryFrame.bind (frame_lift _)
  intro confirmed
  exact receiveTail_quiet pid pkt confirmed

theorem consume_lift (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Driver.consumeObserved hooks pid pkt ep = liftWGPrefix (consumeDataDone pid pkt ep) := by
  apply eq_native_lift _ (consume_quiet pid pkt ep)
  apply native_via_nonce (Driver.consume_projects native_projection pid pkt ep)
    (Driver.consume_projects NativeDriver.nonce_projection pid pkt ep)
  rw [Driver.nonce_consumeObserved_eq]
  exact Nonce.consumeObserved_erases pid pkt ep

/-- Only for side paths that definitionally omit all three changed fields.
No native or exchange claim is made about executing this surrogate driver. -/
private def quietHooks : Driver.Hooks Exchange.Event :=
  {hooks with
    handshake := fun _ _ => liftWGPrefix receiveStep
    flushedSend := fun pid => liftWGPrefix (runFlushedSendWork pid)
    session := fun pid => liftWGPrefix (beginSession pid)}

private theorem quietHooks_history (good : List Exchange.Event → Prop) :
    Driver.HooksHistorySafe good quietHooks where
  deliver := Driver.History.product_lift _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.History.state_lift _
  handshake := fun _ _ _ _ => Driver.History.state_lift _
  fixtureEnter := fun _ => Driver.History.state_pure _
  fixtureLeave := fun _ => Driver.History.state_pure _
  sendWorker := by
    rw [Driver.sendWorker_lift quietHooks rfl]
    exact Driver.History.product_lift _
  flushedSend := fun _ => Driver.History.state_lift _
  armTimer := fun _ _ _ _ => Driver.History.state_lift _
  queueSend := fun _ => Driver.History.state_lift _
  candidateEnter := fun _ _ => Driver.History.product_pure _
  candidateLeave := fun _ => Driver.History.product_pure _
  stackInput := fun _ _ preserves => preserves
  prepare := Driver.History.product_lift _
  counterCheck := fun _ _ => (Driver.History.state_lift _).liftWGObserver
  timerSelected := fun _ _ _ _ _ => Driver.History.product_pure _
  timerFinished := fun _ => Driver.History.product_pure _
  selection := fun _ => Driver.History.state_lift _
  confirmation := fun _ _ => Driver.History.state_lift _
  session := fun _ => Driver.History.state_lift _
  reserve := fun _ => Driver.History.state_lift _
  allocate := fun _ => Driver.History.state_lift _
  create := fun _ _ => Driver.History.state_lift _
  front := fun _ _ _ _ => Driver.History.state_lift _
  poll := Driver.History.product_lift _
  encrypt := fun _ => Driver.History.product_lift _
  transmit := fun _ => Driver.History.product_lift _

private theorem history_frame {g : PrefixM Exchange.Event α}
    (safe : ∀ initial, Driver.ProductHistorySafe (fun h => h = initial) g) : HistoryFrame some g := by
  intro w h
  simpa only [List.filterMap_some] using (safe h w h rfl).choose_spec.2.1

private theorem state_history_frame {g : WGPrefix Exchange.Event α}
    (safe : ∀ initial, Driver.StateHistorySafe (fun h => h = initial) g) : StateHistoryFrame some g := by
  intro w a h
  simpa only [List.filterMap_some] using (safe h w a h rfl).choose_spec.2.1

theorem timer_lift (pid : PeerId) (timer : PeerTimer) :
    Driver.timerObserved hooks pid timer = liftWGPrefix (timerCallback pid timer) := by
  apply eq_native_lift
  · apply native_via_nonce (Driver.timer_projects native_projection pid timer)
      (Driver.timer_projects NativeDriver.nonce_projection pid timer)
    rw [Driver.nonce_timerObserved_eq]
    exact Nonce.timerObserved_erases pid timer
  · apply state_history_frame
    intro initial
    change Driver.StateHistorySafe (fun h => h = initial) (Driver.timerObserved quietHooks pid timer)
    exact Driver.timer_history (quietHooks_history _).core pid timer

theorem product_native_via_nonce {g : PrefixM Exchange.Event α} {n : PrefixM Nonce.Allocation α}
    {empty : PrefixM Empty α} {action : Leanux.M α}
    (pg : ProjectsPrefix NativeDriver.erase id g empty)
    (pn : ProjectsPrefix NativeDriver.erase id n empty)
    (erases : ErasesPrefix n action) : ErasesPrefix g action := by
  intro w h
  have first := congrArg Prod.fst (pg w h)
  have second := congrArg Prod.fst (pn w [])
  have identity : (fun x : α × World => (id x.1,x.2)) = id := by
    funext x
    rcases x with ⟨value,world⟩
    rfl
  simp only [NativeDriver.filter_empty,identity,Except.map_id] at first second
  exact first.symm.trans (second.trans (erases w []))

theorem product_eq_lift {g : PrefixM Exchange.Event α} {action : Leanux.M α}
    (erases : ErasesPrefix g action) (quiet : HistoryFrame some g) : g = liftPrefix action := by
  funext w h
  apply Prod.ext
  · exact erases w h
  · change (runPrefix g w h).2 = h
    simpa only [List.filterMap_some] using quiet w h

theorem nativePoll_quiet (pid : PeerId) (budget : Nat) :
    HistoryFrame some (Driver.nativePollObserved hooks pid budget) := by
  apply history_frame
  intro initial
  change Driver.ProductHistorySafe (fun h => h = initial) (Driver.nativePollObserved quietHooks pid budget)
  exact Driver.nativePoll_history (quietHooks_history _).actors pid budget

theorem nativePoll_lift (pid : PeerId) (budget : Nat) :
    Driver.nativePollObserved hooks pid budget =
      liftPrefix (rxPoll pid budget (fun packets => packets.forM Env.deliverInner)) := by
  apply product_eq_lift _ (nativePoll_quiet pid budget)
  apply product_native_via_nonce (Driver.nativePoll_projects native_projection pid budget)
    (Driver.nativePoll_projects NativeDriver.nonce_projection pid budget)
  rw [Driver.nonce_nativePollObserved_eq]
  exact Nonce.nativePollObserved_erases pid budget

theorem softirq_lift : Driver.softirqObserved hooks = liftPrefix Env.napiSoftirq := by
  apply product_eq_lift
  · apply product_native_via_nonce (Driver.softirq_projects native_projection)
      (Driver.softirq_projects NativeDriver.nonce_projection)
    rw [Driver.nonce_softirqObserved_eq]
    exact Nonce.softirqObserved_erases
  · apply history_frame
    intro initial
    change Driver.ProductHistorySafe (fun h => h = initial) (Driver.softirqObserved quietHooks)
    exact Driver.softirq_history (quietHooks_history _).actors

theorem inline_lift : Driver.inlinePollObserved hooks = liftPrefix Env.pollScheduledInline := by
  apply product_eq_lift
  · apply product_native_via_nonce (Driver.inline_projects native_projection)
      (Driver.inline_projects NativeDriver.nonce_projection)
    rw [Driver.nonce_inlinePollObserved_eq]
    exact Nonce.inlinePollObserved_erases
  · apply history_frame
    intro initial
    change Driver.ProductHistorySafe (fun h => h = initial) (Driver.inlinePollObserved quietHooks)
    exact Driver.inline_history (quietHooks_history _).actors

theorem irqExit_lift : Driver.irqExitObserved hooks = liftPrefix Env.napiIrqExit := by
  apply product_eq_lift
  · apply product_native_via_nonce (Driver.irqExit_projects native_projection)
      (Driver.irqExit_projects NativeDriver.nonce_projection)
    rw [Driver.nonce_irqExitObserved_eq]
    exact Nonce.irqExitObserved_erases
  · apply history_frame
    intro initial
    change Driver.ProductHistorySafe (fun h => h = initial) (Driver.irqExitObserved quietHooks)
    exact Driver.irqExit_history (quietHooks_history _).actors

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriver
