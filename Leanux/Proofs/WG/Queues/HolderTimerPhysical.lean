import Leanux.Proofs.WG.Queues.HolderTimerEnvironment
import Leanux.Proofs.WG.Queues.HolderSendEnvironment

/-! Actual timer atoms retain the physical receive ring as well as their
complete holder account. Concrete crypt/send callbacks share that same run. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTimerPhysical
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders RxRing

private theorem endpoint_cell (pid : PeerId) : SameView nativeCell (clearPeerEndpointSrc pid) := by
  ring_cell_source [clearPeerEndpointSrc, dstCacheResetNow] using [dstCacheReset_cell]

private theorem purge_cell (pid : PeerId) : SameView nativeCell (purgeStagedPackets pid) := by
  ring_cell_source [purgeStagedPackets] using []

private theorem retransmit_cell (pid : PeerId) : SameView nativeCell (expiredRetransmitHandshake pid) := by
  ring_cell_source [expiredRetransmitHandshake] using [delTimer_cell, purge_cell,
    modPeerTimer_cell, endpoint_cell, sendQueuedHandshakeInitiation_cell]

private theorem keepaliveTimer_cell (pid : PeerId) : SameView nativeCell (expiredSendKeepalive pid) := by
  ring_cell_source [expiredSendKeepalive] using [sendKeepalive_cell, modPeerTimer_cell]

private theorem newHandshake_cell (pid : PeerId) : SameView nativeCell (expiredNewHandshake pid) := by
  ring_cell_source [expiredNewHandshake] using [endpoint_cell, sendQueuedHandshakeInitiation_cell]

private theorem zero_cell (pid : PeerId) : SameView nativeCell (expiredZeroKeyMaterial pid) := by
  ring_cell_source [expiredZeroKeyMaterial] using [peerGet_cell, peerPut_cell]

private theorem persistent_cell (pid : PeerId) : SameView nativeCell (expiredSendPersistentKeepalive pid) := by
  ring_cell_source [expiredSendPersistentKeepalive] using [sendKeepalive_cell]

/-- Actual timer callbacks may allocate holders or release a peer; none
changes the device's physical decrypt ring. -/
theorem callback_cell (pid : PeerId) (timer : PeerTimer) : SameView nativeCell (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact retransmit_cell pid
  | sendKeepalive => exact keepaliveTimer_cell pid
  | newHandshake => exact newHandshake_cell pid
  | zeroKeyMaterial => exact zero_cell pid
  | persistentKeepalive => exact persistent_cell pid

private theorem clear_cell (pid : PeerId) : SameView nativeCell (queuedExpiredZeroKeyMaterial pid) := by
  have handshake : SameView nativeCell (handshakeClear pid) := by
    ring_cell_source [handshakeClear, indexRemove] using [handshakeZero_cell]
  have keys : SameView nativeCell (keypairsClear pid) := by
    ring_cell_source [keypairsClear, _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_cell]
  ring_cell_source [queuedExpiredZeroKeyMaterial] using [handshake, keys, peerPut_cell]

theorem flushedClear_cell (pid : PeerId) : SameView nativeCell (runFlushedClearWork pid) := by
  ring_cell_source [runFlushedClearWork] using [clear_cell]

theorem clearOne_cell : SameView RxRing.cell Env.runOneClearWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushedClear_cell pid)
    w.wg beforeWorker () v.wg v.ambient worker

private theorem product_cell (frame : SameProductStore action) : SameView RxRing.cell action :=
  frame.of_factor (fun p : ProductStore43 => p.2.2.2.dev.map fun d => (d.ifindex,d.decryptQueue))
    RxRing.cell (fun _ => rfl)

private theorem native_cell (frame : SameView nativeCell action) : SameView RxRing.cell (liftWG action) :=
  sameView_liftWG RxRing.cell nativeCell action frame (fun _ _ _ h => h)

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World => RxRing.cell w = initial) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

private theorem stored (frame : SameProductStore action) :
    Preserves (fun w : World => RxRing.cell w = initial) action := product_cell frame initial

theorem section_cell (kind : Worker) (body : Leanux.M Unit) (keeps : SameView RxRing.cell body) :
    SameView RxRing.cell (Env.runTimerSection kind body) := by
  have worker := runWorker_sameView RxRing.cell
    (fun _ _ same => congrArg (fun p : ProductStore43 => p.2.2.2.dev.map fun (d : Device) => (d.ifindex,d.decryptQueue)) same)
    kind body keeps
  intro initial
  change Preserves (fun w : World => RxRing.cell w = initial) _
  unfold Env.runTimerSection
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head Env.runWorker; exact worker initial)
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem stepComplete_cell (bucket : UInt64) : SameView RxRing.cell (Env.requireStepComplete bucket) := by
  intro initial
  change Preserves (fun w : World => RxRing.cell w = initial) _
  unfold Env.requireStepComplete
  apply preserves_bind (stored (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none => exact preserves_pure _
  | some pair => cases pair; exact hoare_throw _

macro "timer_cell_product_step" : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact stored (timerWorker_sameKernel _))
  | (rx_retention_head Env.requireStepComplete; exact stepComplete_cell _ _)
  | (rx_retention_head getWG; exact stored (fun initial => productGetWG_spec (fun s => s = initial)))
  | (rx_retention_head modifyWG; exact stored (fun initial => productModifyWG_spec
      (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

theorem dispatch_cell (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    SameView RxRing.cell (timerDispatchUnit kind pid timer entry prior) := by
  intro initial
  change Preserves (fun w : World => RxRing.cell w = initial) _
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact section_cell _ _ (native_cell (callback_cell _ _)) initial)
    | (allocation_release_lift_from WG.M; exact native_cell (delTimer_cell _ _) initial)
    | timer_cell_product_step

theorem placeholder_cell (j : UInt64) : SameView RxRing.cell (RxHistory.placeholderTimerPassSource j) := by
  intro initial
  change Preserves (fun w : World => RxRing.cell w = initial) _
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact section_cell _ _ (native_cell (callback_cell _ _)) initial)
    | (allocation_release_lift_from WG.M; first
        | exact stored (liftWG_sameProductStore getDev getDev_sameWGStore)
        | exact native_cell (delTimer_cell _ _) initial)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => RxRing.cell w = initial)
       intro _ _
       change Preserves (fun w : World => RxRing.cell w = initial) _)
    | timer_cell_product_step

theorem nothingDue_cell (j : UInt64) : SameView RxRing.cell (Env.requireNothingDue j) := by
  have later (kind : Worker) (unit : Nat) : SameProductStore (Env.sectionAppearsLater kind unit) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  intro initial
  change Preserves (fun w : World => RxRing.cell w = initial) _
  unfold Env.requireNothingDue
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact stored (later _ _))
    | timer_cell_product_step

private theorem paired (action : RxHistory.Obs α) (original : Leanux.M α)
    (account : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) action)
    (erase : ErasesPrefix action original) (ring : SameView RxRing.cell original) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) action :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.combine)
    account erase (fun w x v hi run =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.physical_cell)
        hi ((ProjectedAction.iff_run _ _ _).mp ring w x v run))

private theorem idleDevice_cell : SameView RxRing.cell Env.requireIdleDevice := by
  intro initial
  change Preserves (fun w : World => RxRing.cell w = initial) _
  unfold Env.requireIdleDevice
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.requireNoCryptWork; exact stored requireNoCryptWork_sameKernel)
    | (allocation_release_lift_from WG.M
       exact stored (liftWG_sameProductStore getDev getDev_sameWGStore))
    | timer_cell_product_step

/-- Pair the already-funded actual atoms with physical frames of those same
executions. No stronger callback input is forgotten in the join. -/
theorem atoms : RxHistory.DeferredSource.AtomContracts
    (HolderScheduler.Inv initial loans before) (fun _ => True) (fun {_} g => g) := by
  have old := HolderTimerEnvironment.atoms (initial := initial) (loans := loans) (before := before)
  refine ⟨HolderDeferred.sendOne_preserves initial loans before,?_,
    HolderDeferred.drained_preserves initial loans before,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact paired _ _ old.clearOne (RxHistory.audit_erases runOneClearWorkerAudit_erases) clearOne_cell
  · exact paired _ _ old.saved (RxHistory.audit_erases getDevSavedAudit_erases)
      (product_cell (liftWG_sameProductStore getDev getDev_sameWGStore))
  · intro d j
    exact paired _ _ (old.wheel d j) (RxHistory.audit_erases (wheelNextDueAudit_erases d j))
      (SameView.pure _ _)
  · intro bucket
    exact paired _ _ (old.stepComplete bucket) (RxHistory.audit_erases (requireStepCompleteAudit_erases bucket))
      (stepComplete_cell bucket)
  · intro j
    exact paired _ _ (old.nothingDue j) (RxHistory.audit_erases (requireNothingDueAudit_erases j))
      (nothingDue_cell j)
  · intro kind pid timer entry prior
    exact paired _ _ (old.timer kind pid timer entry prior)
      (RxHistory.audit_erases (timerDispatchAudit_erases kind pid timer entry prior))
      (dispatch_cell kind pid timer entry prior)
  · intro j
    exact paired _ _ (old.placeholder j) (RxHistory.audit_erases (RxHistory.placeholderTimerPass_erases j))
      (placeholder_cell j)
  · exact paired _ _ old.idleDevice (RxHistory.mixed_erases requireIdleDevicePrefix_erases) idleDevice_cell
  · exact paired _ _ old.noCrypt (RxHistory.audit_erases (erasesPrefix_lift _))
      (product_cell requireNoCryptWork_sameKernel)
  · intro timer
    exact paired _ _ (old.timerWorker timer) (RxHistory.audit_erases (erasesPrefix_lift _))
      (product_cell (timerWorker_sameKernel timer))
  · intro ticks
    exact paired _ _ (old.advance ticks) (RxHistory.audit_erases (advanceAudit_erases ticks))
      (product_cell (advance_sameKernel ticks))

/-- The record-driven timer loop now uses the concrete crypt scheduler.
Only its original receive-worker account remains an explicit contract. -/
theorem runTimers_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) (j : UInt64) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) (RxHistory.runTimers j) := by
  rw [RxHistory.DeferredSource.timers_factor]
  exact RxHistory.DeferredSource.timers_preserves
    (I := HolderScheduler.Inv initial loans before) (S := fun _ => True)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => HolderScheduler.store hi same)
    _ atoms _ (HolderDeferred.runCryptWorkers_preserves initial loans before receive) j

theorem placeholder_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) (j : UInt64) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor]
  exact RxHistory.DeferredSource.placeholder_preserves
    (I := HolderScheduler.Inv initial loans before) (S := fun _ => True)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => HolderScheduler.store hi same)
    _ atoms _ (HolderDeferred.runCryptWorkers_preserves initial loans before receive)
    _ (HolderDeferred.runSendWorkers_preserves initial loans before receive) j

theorem idle_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact RxHistory.DeferredSource.idle_preserves
    (I := HolderScheduler.Inv initial loans before) (S := fun _ => True)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => HolderScheduler.store hi same)
    _ atoms _ (runTimers_preserves initial loans before receive)
    _ (placeholder_preserves initial loans before receive)

theorem afterAdvance_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact RxHistory.DeferredSource.afterAdvance_preserves
    (I := HolderScheduler.Inv initial loans before) (S := fun _ => True)
    (fun _ _ _ => True.intro) (fun _ _ _ same hi => HolderScheduler.store hi same)
    _ atoms _ (runTimers_preserves initial loans before receive)
    _ (placeholder_preserves initial loans before receive)

/-- Every deferred constructor uses its original observer and dispatch
position. Stops retain their real journal prefix; no Stop state is invented. -/
theorem deferred_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration) (call : EnvDeferredCall) :
    PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) (RxHistory.deferred call) := by
  rw [RxHistory.DeferredSource.deferred_factor]
  exact RxHistory.DeferredSource.deferred_preserves
    (I := HolderScheduler.Inv initial loans before) (S := fun _ => True)
    _ atoms _ _ _ _ _ _ _
    (HolderDeferred.runCryptWorkers_preserves initial loans before receive)
    (HolderDeferred.runSendWorkers_preserves initial loans before receive)
    (HolderDeferred.afterXmit_preserves initial loans before receive)
    (runTimers_preserves initial loans before receive)
    (placeholder_preserves initial loans before receive)
    (idle_preserves initial loans before receive)
    (afterAdvance_preserves initial loans before receive) call

/-- Funding and the physical witness are read at the same actual native
endpoint, using precisely that execution's committed removal suffix. -/
theorem runTimers_normal (j : UInt64) (h : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv cs loans h) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration)
    (funded : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : (Env.runTimers j).run w = .ok (result,v)) :
    (∃ suffix, (runPrefix (RxHistory.runTimers j) w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      DecryptIteration.Physical v :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.native_result)
    (runTimers_preserves cs loans h receive j) (RxHistory.runTimers_erases j) funded physical run

theorem afterAdvance_normal (h : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv cs loans h) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration)
    (funded : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : Env.afterAdvance.run w = .ok ((),v)) :
    (∃ suffix, (runPrefix RxHistory.afterAdvance w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      DecryptIteration.Physical v :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.native_result)
    (afterAdvance_preserves cs loans h receive) RxHistory.afterAdvance_erases funded physical run

theorem deferred_normal (call : EnvDeferredCall) {result : call.Result} (h : List RxHistory.Event)
    (receive : PrefixPreserves (HolderScheduler.Inv cs loans h) (fun _ => True)
      Origins.HistoryAdapters.receiveIteration)
    (funded : Boundary cs loans w.wg) (physical : DecryptIteration.Physical w)
    (run : call.original.run w = .ok (result,v)) :
    (∃ suffix, (runPrefix (RxHistory.deferred call) w h).2 = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg) ∧
      DecryptIteration.Physical v :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.native_result)
    (deferred_preserves cs loans h receive call) (RxHistory.deferred_erases call) funded physical run

end Leanux.Proofs.WG.Queues.RxCredits.HolderTimerPhysical
