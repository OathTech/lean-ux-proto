import Leanux.Proofs.WG.Queues.HolderTimerCallbacks
import Leanux.Proofs.WG.Queues.HolderEncryptHistory
import Leanux.Proofs.WG.Queues.HolderSendDispatch
import Leanux.Proofs.WG.Queues.HolderClearDispatch
import Leanux.Proofs.WG.Queues.DeferredPreservation

/-! The original timer wheel's dispatch retains complete holder funding.
Recorded guards and detached timer state remain at their actual source cuts. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderTimerEnvironment
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem stored (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World => Boundary cs loans w.wg) action :=
  HolderEncrypt.product_store_boundary same

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World => Boundary cs loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

theorem worker (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World => Boundary cs loans w.wg) body) :
    Preserves (fun w : World => Boundary cs loans w.wg) (Env.runWorker kind body) := by
  unfold Env.runWorker
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | exact keeps
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem section_boundary (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World => Boundary cs loans w.wg) body) :
    Preserves (fun w : World => Boundary cs loans w.wg) (Env.runTimerSection kind body) := by
  unfold Env.runTimerSection
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head Env.runWorker; exact worker kind body keeps)
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem stepComplete (bucket : UInt64) :
    Preserves (fun w : World => Boundary cs loans w.wg) (Env.requireStepComplete bucket) := by
  unfold Env.requireStepComplete
  apply preserves_bind (stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none => exact preserves_pure _
  | some pair => cases pair; exact hoare_throw _

macro "holder_timer_product_step" : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact stored _ (timerWorker_sameKernel _))
  | (rx_retention_head Env.requireStepComplete; exact stepComplete _)
  | (rx_retention_head getWG; exact stored _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (rx_retention_head modifyWG; exact stored _ (fun initial => productModifyWG_spec
      (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

/-- The recorded worker and timer address are checked before detachment.
The original callback runs with the same caller loans and a funded account. -/
theorem dispatch (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    Preserves (fun w : World => Boundary cs loans w.wg)
      (timerDispatchUnit kind pid timer entry prior) := by
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact section_boundary _ _ (HolderTimers.callback_product _ _))
    | (allocation_release_lift_from WG.M
       exact HolderEncrypt.lift_boundary (HolderTimers.delTimer_boundary _ _))
    | holder_timer_product_step

/-- The domain-filter pass uses its original saved pending count and fresh
wheel selection each turn, including callback rearming and source Stops. -/
theorem placeholderPass (jHi : UInt64) :
    Preserves (fun w : World => Boundary cs loans w.wg) (RxHistory.placeholderTimerPassSource jHi) := by
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact section_boundary _ _ (HolderTimers.callback_product _ _))
    | (allocation_release_lift_from WG.M; first
        | exact stored _ (liftWG_sameProductStore getDev getDev_sameWGStore)
        | exact HolderEncrypt.lift_boundary (HolderTimers.delTimer_boundary _ _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => Boundary cs loans w.wg)
       intro _ _
       change Preserves (fun w : World => Boundary cs loans w.wg) _)
    | holder_timer_product_step

/-- Advancing the clock changes no charged holder or receive carrier. -/
theorem advance (ticks : Nat) :
    Preserves (fun w : World => Boundary cs loans w.wg) (Env.advance ticks) :=
  stored _ (advance_sameKernel ticks)

theorem nothingDue (j : UInt64) :
    Preserves (fun w : World => Boundary cs loans w.wg) (Env.requireNothingDue j) := by
  have later (kind : Worker) (unit : Nat) :
      Preserves (fun w : World => Boundary cs loans w.wg) (Env.sectionAppearsLater kind unit) :=
    stored _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v run
      cases run
      rfl)
  unfold Env.requireNothingDue
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact later _ _)
    | holder_timer_product_step

/-- A real audit-only subtree appends no RX removal event. Its original
execution transports the ledger at the existing, arbitrary history cut. -/
theorem audit_at (g : AuditM α) (a : Leanux.M α) (erase : ErasesPrefix g a)
    (keeps : ∀ cs, Preserves (fun w : World => Boundary cs loans w.wg) a) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.audit g) := by
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h x v hi run
  obtain ⟨old,history,stable⟩ := hi
  have original := (RxHistory.audit_erases erase w h).symm.trans run
  apply HolderDecryptHistory.quiet_cut (Appends.focus _ _ _) _ history (Prod.ext run rfl)
    ((hoare_iff_run _ _ _).mp (keeps _) w x v stable original)
  intro w h
  exact focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent NapiCarrier.removed
    (fun _ => rfl) g w h

theorem dispatch_at (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit (timerDispatchAudit kind pid timer entry prior)) :=
  audit_at _ _ (timerDispatchAudit_erases _ _ _ _ _) (fun _ => dispatch _ _ _ _ _)

theorem placeholderPass_at (j : UInt64) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  audit_at _ _ (RxHistory.placeholderTimerPass_erases j) (fun _ => placeholderPass j)

private theorem saved_at :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit getDevSavedAudit) :=
  audit_at _ _ getDevSavedAudit_erases
    (fun _ => stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))

private theorem wheel_at (d : Device) (j : UInt64) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit (wheelNextDueAudit d j)) :=
  audit_at _ _ (wheelNextDueAudit_erases d j) (fun _ => preserves_pure _)

theorem sendOne_at :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit runOneSendWorkerAudit) := by
  apply audit_at _ _ runOneSendWorkerAudit_erases
  intro cs
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases x
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨pid,o,rest,_,post,stable⟩ := runOneSendWorker_funded w v funded stable run
  exact ⟨holders.withoutSend rest,post,stable⟩

theorem clearOne_at :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit runOneClearWorkerAudit) := by
  apply audit_at _ _ runOneClearWorkerAudit_erases
  intro cs
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases x
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨pid,o,rest,_,post,stable⟩ := runOneClearWorker_funded w v funded stable run
  exact ⟨holders.withoutClear rest,post,stable⟩

private theorem step_at (bucket : UInt64) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  audit_at _ _ (requireStepCompleteAudit_erases bucket) (fun _ => stepComplete bucket)

theorem nothing_at (j : UInt64) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit (requireNothingDueAudit j)) :=
  audit_at _ _ (requireNothingDueAudit_erases j) (fun _ => nothingDue j)

theorem advance_at (ticks : Nat) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.audit (advanceAudit ticks)) :=
  audit_at _ _ (erasesPrefix_lift _) (fun _ => advance ticks)

private theorem drained_source (what : String) (queues : List Bool) :
    Preserves (fun w : World => Boundary cs loans w.wg) (Env.requireDrained what queues) := by
  unfold Env.requireDrained
  simp (config := {zeta := false}) only [unsupported,invariant,pendingDeviceUnits]
  repeat' first
    | (allocation_release_lift_from WG.M
       exact stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))
    | holder_timer_product_step

private theorem idleDevice_source :
    Preserves (fun w : World => Boundary cs loans w.wg) Env.requireIdleDevice := by
  unfold Env.requireIdleDevice
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.requireNoCryptWork; exact stored _ requireNoCryptWork_sameKernel)
    | (allocation_release_lift_from WG.M
       exact stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))
    | holder_timer_product_step

private theorem mixed_at (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erase : ErasesPrefix g a)
    (keeps : ∀ cs, Preserves (fun w : World => Boundary cs loans w.wg) a) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.mixed g) := by
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h x v hi run
  exact HolderEncrypt.mixed_at g a erase keeps hi (Prod.ext run rfl)

/-- Every exact poll-free atom of the existing deferred source preserves this
account. Saved scans use their actual getter/erasure, with no invented funds. -/
theorem atoms : RxHistory.DeferredSource.AtomContracts
    (HolderNapi.At initial loans before) (fun _ => True) (fun {_} g => g) := by
  refine ⟨sendOne_at,clearOne_at,?_,saved_at,wheel_at,step_at,nothing_at,
    dispatch_at,placeholderPass_at,?_,?_,?_,advance_at⟩
  · intro what queues
    exact mixed_at _ _ (requireDrainedPrefix_erases what queues) (fun _ => drained_source what queues)
  · exact mixed_at _ _ requireIdleDevicePrefix_erases (fun _ => idleDevice_source)
  · exact audit_at _ _ (erasesPrefix_lift _) (fun _ => stored _ requireNoCryptWork_sameKernel)
  · intro timer
    exact audit_at _ _ (erasesPrefix_lift _) (fun _ => stored _ (timerWorker_sameKernel timer))

/-- The original record-driven loop retains the fixed accounting cut.
The actual crypt scheduler's contract is explicit because it can remove RX
carriers and must update this same journal-derived ledger. -/
theorem runTimers (j : UInt64)
    (crypt : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) (RxHistory.runTimers j) := by
  rw [RxHistory.DeferredSource.timers_factor]
  exact RxHistory.DeferredSource.timers_preserves (I := HolderNapi.At initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => HolderNapi.store hi same) _ atoms _ crypt j

/-- The placeholder retains the original crypt and send observers at their
source call positions; neither callback is assumed independent of history. -/
theorem runTimersPlaceholder (j : UInt64)
    (crypt : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers)
    (send : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      RxHistory.runSendWorkers) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor]
  exact RxHistory.DeferredSource.placeholder_preserves (I := HolderNapi.At initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => HolderNapi.store hi same) _ atoms _ crypt _ send j

theorem idleTimers
    (crypt : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers)
    (send : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      RxHistory.runSendWorkers) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact RxHistory.DeferredSource.idle_preserves (I := HolderNapi.At initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => HolderNapi.store hi same) _ atoms
    _ (fun j => runTimers j crypt) _ (fun j => runTimersPlaceholder j crypt send)

theorem afterAdvance
    (crypt : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers)
    (send : PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True)
      RxHistory.runSendWorkers) :
    PrefixPreserves (HolderNapi.At initial loans before) (fun _ => True) RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact RxHistory.DeferredSource.afterAdvance_preserves (I := HolderNapi.At initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => HolderNapi.store hi same) _ atoms
    _ (fun j => runTimers j crypt) _ (fun j => runTimersPlaceholder j crypt send)

/-- The endpoint account is obtained from the same original execution and its
own appended removal suffix. This assertion says nothing about a Stop state. -/
theorem normal (g : RxHistory.Obs α) (a : Leanux.M α) (erase : ErasesPrefix g a)
    (keeps : PrefixPreserves (HolderNapi.At cs loans h) (fun _ => True) g)
    (hi : Boundary cs loans w.wg) (run : a.run w = .ok (result,v)) :
    let k := (runPrefix g w h).2
    ∃ suffix, k = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg := by
  have actual := (erase w h).trans run
  have post := (keeps w h (HolderNapi.at_start hi h)).choose_spec.2.2
  simpa only [actual,HolderNapi.At] using post

theorem runTimers_normal (j : UInt64) (h : List RxHistory.Event)
    (crypt : PrefixPreserves (HolderNapi.At cs loans h) (fun _ => True) RxHistory.runCryptWorkers)
    (hi : Boundary cs loans w.wg) (run : (Env.runTimers j).run w = .ok (result,v)) :
    let k := (runPrefix (RxHistory.runTimers j) w h).2
    ∃ suffix, k = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg :=
  normal _ _ (RxHistory.runTimers_erases j) (runTimers j crypt) hi run

theorem afterAdvance_normal (h : List RxHistory.Event)
    (crypt : PrefixPreserves (HolderNapi.At cs loans h) (fun _ => True) RxHistory.runCryptWorkers)
    (send : PrefixPreserves (HolderNapi.At cs loans h) (fun _ => True) RxHistory.runSendWorkers)
    (hi : Boundary cs loans w.wg) (run : Env.afterAdvance.run w = .ok ((),v)) :
    let k := (runPrefix RxHistory.afterAdvance w h).2
    ∃ suffix, k = h ++ suffix ∧
      Boundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg :=
  normal _ _ RxHistory.afterAdvance_erases (afterAdvance crypt send) hi run

end Leanux.Proofs.WG.Queues.RxCredits.HolderTimerEnvironment
