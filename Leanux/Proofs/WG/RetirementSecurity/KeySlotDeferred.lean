import Leanux.Proofs.WG.RetirementSecurity.KeySlotScheduler
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeferred
import Leanux.Proofs.WG.Queues.TxLiveDeferred
import Leanux.Proofs.WG.Queues.RxWaitAppends

/-! Actual deferred worker and timer paths preserve live published key slots.
Existing source factors retain recorded wheel selection, placeholder paths,
worker drains and explicit stops. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotDeferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open KeySlotLiveness Queues.RxCredits
variable {pending : List PeerId}

abbrev Inv (pending : List PeerId)
    (_ : List RxHistory.Event) (w : World) := InvExcept pending w.wg

private theorem product_store (same : productStoreView v = productStoreView w)
    (before : InvExcept pending w.wg) : InvExcept pending v.wg :=
  store_transport (congrArg (fun s : ProductStore43 => s.2.2.2) same) before

private theorem stored (frame : SameProductStore action) :
    Preserves (fun w : World => InvExcept pending w.wg) action :=
  KeySlotLiveness.product_store frame

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World => InvExcept pending w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ before => before)

private theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => InvExcept pending w.wg) a) :
    PrefixPreserves (fun _ w => InvExcept pending w.wg) (fun _ => True) g :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.KeySlotNapi.«0».Leanux.Proofs.WG.RetirementSecurity.KeySlotNapi.observed)
    pending g a appends erases keeps

private theorem native (g : RxHistory.Obs α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (keeps : PrefixPreserves (Inv pending) (fun _ => True) g) :
    Preserves (fun w : World => InvExcept pending w.wg) a :=
  (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.KeySlotNapi.«0».Leanux.Proofs.WG.RetirementSecurity.KeySlotNapi.native)
    pending g a erases keeps

theorem send_one : Preserves (fun w : World=>InvExcept pending w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_send pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem clear_one : Preserves (fun w : World=>InvExcept pending w.wg) Env.runOneClearWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    ClearWork.runOneClearWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (flushed_clear pid)
    w.wg beforeWorker () v.wg v.ambient before worker

theorem schedule_observed (stack : Option Worker) :
    PrefixPreserves (Inv pending) (fun _ => True) (RxHistory.schedule stack) :=
  observed _ _ (RxHistory.schedule_appends stack) (RxHistory.schedule_erases stack)
    (KeySlotScheduler.schedule stack)

theorem timerSection (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World=>InvExcept pending w.wg) body) :
    Preserves (fun w : World=>InvExcept pending w.wg) (Env.runTimerSection kind body) := by
  have worker : Preserves (fun w : World=>InvExcept pending w.wg) (Env.runWorker kind body) :=
    native (runWorkerPrefix (Event:=RxHistory.Event) kind (liftPrefix body)) _
      (runWorkerPrefix_erases kind (erasesPrefix_lift _))
      (runWorkerPrefix_preserves (fun _ _ _=>True.intro)
        (fun _ _ _ eq hi=>product_store eq hi) kind
        (observed _ _ (Appends.lift _) (erasesPrefix_lift _) keeps))
  unfold Env.runTimerSection
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head Env.runWorker; exact worker)
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem stepComplete (bucket : UInt64) :
    Preserves (fun w : World=>InvExcept pending w.wg) (Env.requireStepComplete bucket) := by
  unfold Env.requireStepComplete
  apply preserves_bind (stored (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none=>exact preserves_pure _
  | some pair=>cases pair; exact hoare_throw _

macro "occurrence_deferred_product_step" : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact stored (timerWorker_sameKernel _))
  | (rx_retention_head Env.requireStepComplete; exact stepComplete _)
  | (rx_retention_head getWG; exact stored (fun initial=>productGetWG_spec (fun s=>s=initial)))
  | (rx_retention_head modifyWG; exact stored (fun initial=>productModifyWG_spec
      (fun s=>s=initial) _ (fun _=>rfl)))
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

theorem timerDispatch (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    Preserves (fun w : World=>InvExcept pending w.wg) (timerDispatchUnit kind pid timer entry prior) := by
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact timerSection _ _ (PublicationPoll.native_product (InvExcept pending) _ (KeySlotLiveness.timer _ _)))
    | (allocation_release_lift_from WG.M
       exact PublicationPoll.native_product (InvExcept pending) _ (KeySlotLiveness.del_timer _ _))
    | occurrence_deferred_product_step

theorem placeholderTimer (j : UInt64) :
    Preserves (fun w : World=>InvExcept pending w.wg) (RxHistory.placeholderTimerPassSource j) := by
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact timerSection _ _ (PublicationPoll.native_product (InvExcept pending) _ (KeySlotLiveness.timer _ _)))
    | (allocation_release_lift_from WG.M; first
        | exact stored (liftWG_sameProductStore getDev getDev_sameWGStore)
        | exact PublicationPoll.native_product (InvExcept pending) _ (KeySlotLiveness.del_timer _ _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World=>InvExcept pending w.wg)
       intro _ _
       change Preserves (fun w : World=>InvExcept pending w.wg) _)
    | occurrence_deferred_product_step

theorem nothingDue (j : UInt64) :
    Preserves (fun w : World=>InvExcept pending w.wg) (Env.requireNothingDue j) := by
  have later (kind : Worker) (unit : Nat) : SameProductStore (Env.sectionAppearsLater kind unit) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v run
    cases run
    rfl
  unfold Env.requireNothingDue
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact stored (later _ _))
    | occurrence_deferred_product_step

theorem drained (what : String) (queues : List Bool) :
    Preserves (fun w : World=>InvExcept pending w.wg) (Env.requireDrained what queues) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  exact (requireDrained_normal what queues w v run).1 ▸ hi

theorem idleDevice : Preserves (fun w : World=>InvExcept pending w.wg) Env.requireIdleDevice := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  exact (idleDevice_normal w v run).1 ▸ hi

theorem atoms : RxHistory.DeferredSource.AtomContracts
    (Inv pending) (fun _=>True) (fun {_} g=>g) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases runOneSendWorkerAudit_erases) send_one
  · exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases runOneClearWorkerAudit_erases) clear_one
  · intro what queues
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases (requireDrainedPrefix_erases what queues)) (drained what queues)
  · exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases getDevSavedAudit_erases)
      (stored (liftWG_sameProductStore getDev getDev_sameWGStore))
  · intro d j
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (wheelNextDueAudit_erases d j)) (preserves_pure _)
  · intro bucket
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (requireStepCompleteAudit_erases bucket)) (stepComplete bucket)
  · intro j
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (requireNothingDueAudit_erases j)) (nothingDue j)
  · intro kind pid timer entry prior
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (timerDispatchAudit_erases kind pid timer entry prior)) (timerDispatch kind pid timer entry prior)
  · intro j
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (RxHistory.placeholderTimerPass_erases j)) (placeholderTimer j)
  · exact observed _ _ (Appends.focus _ _ _) (RxHistory.mixed_erases requireIdleDevicePrefix_erases) idleDevice
  · exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (erasesPrefix_lift _)) (stored requireNoCryptWork_sameKernel)
  · intro timer
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (erasesPrefix_lift _)) (stored (timerWorker_sameKernel timer))
  · intro ticks
    exact observed _ _ (Appends.focus _ _ _) (RxHistory.audit_erases (advanceAudit_erases ticks)) (stored (advance_sameKernel ticks))

theorem crypt : PrefixPreserves (Inv pending) (fun _=>True) RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves (I:=(Inv pending))
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ (schedule_observed none)

theorem send : PrefixPreserves (Inv pending) (fun _=>True) RxHistory.runSendWorkers := by
  rw [RxHistory.DeferredSource.send_factor]
  exact RxHistory.DeferredSource.send_preserves (I:=(Inv pending))
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ atoms _ (schedule_observed none)

theorem afterXmit : PrefixPreserves (Inv pending) (fun _=>True) RxHistory.afterXmit := by
  rw [RxHistory.DeferredSource.afterXmit_factor]
  exact RxHistory.DeferredSource.afterXmit_preserves (I:=(Inv pending))
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ atoms _ crypt _ send

theorem timers (j : UInt64) : PrefixPreserves (Inv pending) (fun _=>True) (RxHistory.runTimers j) := by
  rw [RxHistory.DeferredSource.timers_factor]
  exact RxHistory.DeferredSource.timers_preserves (I:=(Inv pending))
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ atoms _ crypt j

theorem placeholder (j : UInt64) : PrefixPreserves (Inv pending) (fun _=>True) (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor]
  exact RxHistory.DeferredSource.placeholder_preserves (I:=(Inv pending))
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ atoms _ crypt _ send j

theorem idle : PrefixPreserves (Inv pending) (fun _=>True) RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact RxHistory.DeferredSource.idle_preserves (I:=(Inv pending))
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ atoms _ timers _ placeholder

theorem afterAdvance : PrefixPreserves (Inv pending) (fun _=>True) RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact RxHistory.DeferredSource.afterAdvance_preserves (I:=(Inv pending))
    (fun _ _ _=>True.intro) (fun _ _ _ eq hi=>product_store eq hi) _ atoms _ timers _ placeholder

theorem deferred (call : EnvDeferredCall) :
    PrefixPreserves (Inv pending) (fun _=>True) (RxHistory.deferred call) := by
  rw [RxHistory.DeferredSource.deferred_factor]
  exact RxHistory.DeferredSource.deferred_preserves (I:=(Inv pending)) (S:=fun _=>True)
    _ atoms _ _ _ _ _ _ _ crypt send afterXmit timers placeholder idle afterAdvance call

/-- Actual deferred calls preserve live slot publication. This is safety
transport through the selected wheel and work source, not eventual disposal. -/
theorem original (call : EnvDeferredCall) :
    Preserves (fun w : World => InvExcept pending w.wg) call.original :=
  native _ _ (RxHistory.deferred_erases call) (deferred call)

end Leanux.Proofs.WG.RetirementSecurity.KeySlotDeferred
