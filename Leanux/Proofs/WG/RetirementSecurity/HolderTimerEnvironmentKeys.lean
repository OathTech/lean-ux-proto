import Leanux.Proofs.WG.RetirementSecurity.HolderTimerKeys

/-! Native timer dispatch keeps the callback's actual entry premises across
record selection, timer detachment and section bookkeeping. No clock progress
or worker fairness is assumed by these preservation contracts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderTimerKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

def ProductReady (temporary : Credits.Ledger) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (w : World) :=
  HolderScheduled.Extra temporary locals active w ∧ CurrentSlots.Inv w.wg

theorem product_store (entry : ProductReady temporary locals active w)
    (same : productStoreView v=productStoreView w) : ProductReady temporary locals active v :=
  ⟨HolderScheduled.extra_store entry.1 same,CurrentSlots.fields_transport entry.2
    (by have device := congrArg (fun s:ProductStore43=>s.2.2.2.dev) same
        change v.wg.dev=w.wg.dev at device
        unfold CurrentSlots.fields RxCredits.keyWords; rw [device])⟩

theorem stored {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (ProductReady temporary locals active) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  exact product_store entry ((ProjectedAction.iff_run _ _ _).mp same w result v run)

theorem native_callback (pid : PeerId) (timer : PeerTimer) :
    Preserves (ProductReady temporary locals active) (liftWG (timerCallback pid timer)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  have native := HolderPoll.native_receipt run
  have kept := (hoare_iff_run_ambient _ _ _).mp (callback pid timer)
    w.wg w.ambient result v.wg v.ambient ⟨entry.1.1,entry.1.2.1.1,entry.2⟩ native
  exact ⟨⟨kept.1,(hoare_iff_run_ambient _ _ _).mp (OccurrenceTimers.callback pid timer)
      w.wg w.ambient result v.wg v.ambient entry.1.2.1 native,
    BaseCoherence.transport entry.1.2.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp
      (BaseCoherence.timerCallback_view pid timer) w.wg w.ambient result v.wg v.ambient native),
    (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.timer (pending:=[]) pid timer)
      w.wg w.ambient result v.wg v.ambient entry.1.2.2.2 native⟩,kept.2.2⟩

theorem del_timer (pid : PeerId) (timer : PeerTimer) :
    Preserves (ProductReady temporary locals active) (liftWG (delTimer pid timer)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  have native := HolderPoll.native_receipt run
  exact ⟨⟨entry.1.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp (delTimer_ownership pid timer)
      w.wg w.ambient result v.wg v.ambient native),
    (hoare_iff_run_ambient _ _ _).mp (OccurrenceTimers.maintenance (.deleteTimer pid timer))
      w.wg w.ambient result v.wg v.ambient entry.1.2.1 native,
    BaseCoherence.transport entry.1.2.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp
      (BaseCoherence.delTimer_view pid timer) w.wg w.ambient result v.wg v.ambient native),
    (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.del_timer (pending:=[]) pid timer)
      w.wg w.ambient result v.wg v.ambient entry.1.2.2.2 native⟩,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.delTimer_preserves pid timer)
      w.wg w.ambient result v.wg v.ambient entry.2 native⟩

theorem ambient (action : AmbientM α) :
    Preserves (ProductReady temporary locals active) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ entry=>entry)

theorem worker (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (ProductReady temporary locals active) body) :
    Preserves (ProductReady temporary locals active) (Env.runWorker kind body) := by
  unfold Env.runWorker
  simp (config:={zeta:=false}) only [hidden]
  repeat' first
    | exact keeps
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem timer_section (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (ProductReady temporary locals active) body) :
    Preserves (ProductReady temporary locals active) (Env.runTimerSection kind body) := by
  unfold Env.runTimerSection
  simp (config:={zeta:=false}) only [invariant]
  repeat' first
    | (rx_retention_head Env.runWorker; exact worker kind body keeps)
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem step_complete (bucket : UInt64) :
    Preserves (ProductReady temporary locals active) (Env.requireStepComplete bucket) := by
  unfold Env.requireStepComplete
  apply preserves_bind (stored (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none=>exact preserves_pure _
  | some pair=>cases pair; exact hoare_throw _

macro "holder_timer_product_step" : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact stored (timerWorker_sameKernel _))
  | (rx_retention_head Env.requireStepComplete; exact step_complete _)
  | (rx_retention_head getWG; exact stored (fun initial=>productGetWG_spec (fun s=>s=initial)))
  | (rx_retention_head modifyWG; exact stored (fun initial=>productModifyWG_spec
      (fun s=>s=initial) _ (fun _=>rfl)))
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

theorem dispatch (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    Preserves (ProductReady temporary locals active) (timerDispatchUnit kind pid timer entry prior) := by
  unfold timerDispatchUnit
  simp (config:={zeta:=false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection; exact timer_section _ _ (native_callback _ _))
    | (allocation_release_lift_from WG.M; exact del_timer _ _)
    | holder_timer_product_step

theorem placeholder (j : UInt64) :
    Preserves (ProductReady temporary locals active) (RxHistory.placeholderTimerPassSource j) := by
  unfold RxHistory.placeholderTimerPassSource
  simp (config:={zeta:=false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection; exact timer_section _ _ (native_callback _ _))
    | (allocation_release_lift_from WG.M; first
        | exact stored (liftWG_sameProductStore getDev getDev_sameWGStore)
        | exact del_timer _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (ProductReady temporary locals active)
       intro _ _
       change Preserves (ProductReady temporary locals active) _)
    | holder_timer_product_step

theorem nothing_due (j : UInt64) :
    Preserves (ProductReady temporary locals active) (Env.requireNothingDue j) := by
  have later (kind : Worker) (unit : Nat) : SameProductStore (Env.sectionAppearsLater kind unit) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result v run
    cases run
    rfl
  unfold Env.requireNothingDue
  simp (config:={zeta:=false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact stored (later _ _))
    | holder_timer_product_step

end Leanux.Proofs.WG.RetirementSecurity.HolderTimerKeys
