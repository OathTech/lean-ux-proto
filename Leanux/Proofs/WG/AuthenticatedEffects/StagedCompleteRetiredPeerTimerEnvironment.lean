import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWorkDispatch
import Leanux.Proofs.WG.Queues.HolderTimerEnvironment

/-! Native recorded and placeholder timer dispatch preserves the exact peer
account. The original RX-removal journal stays attached to the same run;
crypt/send scheduler contracts remain explicit. These contracts constrain
normal endpoints and do not invent a state after Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.TimerEnvironment
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders

private theorem lift_boundary {action : WG.M α}
    (keeps : Preserves (ExactBoundary cs loans) action) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient x v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v x run)

private theorem stored (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) action :=
  by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact hi.store (congrArg (fun p : ProductStore43 => p.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w x v run))

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

theorem worker (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World => ExactBoundary cs loans w.wg) body) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.runWorker kind body) := by
  unfold Env.runWorker
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | exact keeps
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem section_boundary (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World => ExactBoundary cs loans w.wg) body) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.runTimerSection kind body) := by
  unfold Env.runTimerSection
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head Env.runWorker; exact worker kind body keeps)
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem stepComplete (bucket : UInt64) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.requireStepComplete bucket) := by
  unfold Env.requireStepComplete
  apply preserves_bind (stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none => exact preserves_pure _
  | some pair => cases pair; exact hoare_throw _

macro "retired_timer_product_step" : tactic => `(tactic| first
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
    Preserves (fun w : World => ExactBoundary cs loans w.wg)
      (timerDispatchUnit kind pid timer entry prior) := by
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact section_boundary _ _ (TimerCallbacks.callback_product _ _))
    | (allocation_release_lift_from WG.M
       exact lift_boundary (TimerCallbacks.delTimer_boundary _ _))
    | retired_timer_product_step

/-- The domain-filter pass uses its original saved pending count and fresh
wheel selection each turn, including callback rearming and source Stops. -/
theorem placeholderPass (jHi : UInt64) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (RxHistory.placeholderTimerPassSource jHi) := by
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection
       exact section_boundary _ _ (TimerCallbacks.callback_product _ _))
    | (allocation_release_lift_from WG.M; first
        | exact stored _ (liftWG_sameProductStore getDev getDev_sameWGStore)
        | exact lift_boundary (TimerCallbacks.delTimer_boundary _ _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => ExactBoundary cs loans w.wg)
       intro _ _
       change Preserves (fun w : World => ExactBoundary cs loans w.wg) _)
    | retired_timer_product_step

/-- Advancing the clock changes no charged holder or receive carrier. -/
theorem advance (ticks : Nat) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.advance ticks) :=
  stored _ (advance_sameKernel ticks)

theorem nothingDue (j : UInt64) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.requireNothingDue j) := by
  have later (kind : Worker) (unit : Nat) :
      Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.sectionAppearsLater kind unit) :=
    stored _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v run
      cases run
      rfl)
  unfold Env.requireNothingDue
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.sectionAppearsLater; exact later _ _)
    | retired_timer_product_step

/-- A history-only append does not change the remaining RX ledger. Its
native action still needs the full exact-account contract. -/
theorem kept_at (g : RxHistory.Obs α) (a : Leanux.M α)
    (erase : ErasesPrefix g a) (appends : Appends g)
    (quiet : ∀ w h, NapiCarrier.removedPackets (runPrefix g w h).2 =
      NapiCarrier.removedPackets h)
    (keeps : ∀ cs, Preserves (fun w : World => ExactBoundary cs loans w.wg) a) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) g := by
  apply NapiCarrier.normal_spec appends
  intro w h x v hi run
  obtain ⟨old,history,account⟩ := hi
  obtain ⟨extra,extended⟩ := appends w h
  have empty : NapiCarrier.removedPackets extra = [] := by
    have equation := quiet w h
    rw [extended] at equation
    exact List.append_cancel_left (by
      simpa only [NapiCarrier.removedPackets,List.filterMap_append,List.append_nil] using equation)
  have native := (erase w h).symm.trans run
  have kept := (hoare_iff_run _ _ _).mp (keeps _) w x v account native
  refine ⟨old ++ extra,by rw [extended,history,List.append_assoc],?_⟩
  simp only [NapiCarrier.removedPackets,List.filterMap_append]
  change ExactBoundary (remaining initial
    (NapiCarrier.removedPackets old ++ NapiCarrier.removedPackets extra)) loans v.wg
  rw [empty,List.append_nil]
  exact kept

theorem audit_at (g : AuditM α) (a : Leanux.M α) (erase : ErasesPrefix g a)
    (keeps : ∀ cs, Preserves (fun w : World => ExactBoundary cs loans w.wg) a) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) (RxHistory.audit g) :=
  kept_at _ _ (RxHistory.audit_erases erase) (Appends.focus _ _ _)
    (fun w h => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent NapiCarrier.removed
      (fun _ => rfl) g w h) keeps

theorem dispatch_at (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit (timerDispatchAudit kind pid timer entry prior)) :=
  audit_at _ _ (timerDispatchAudit_erases _ _ _ _ _) (fun _ => dispatch _ _ _ _ _)

theorem placeholderPass_at (j : UInt64) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  audit_at _ _ (RxHistory.placeholderTimerPass_erases j) (fun _ => placeholderPass j)

private theorem saved_at :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit getDevSavedAudit) :=
  audit_at _ _ getDevSavedAudit_erases
    (fun _ => stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))

private theorem wheel_at (d : Device) (j : UInt64) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit (wheelNextDueAudit d j)) :=
  audit_at _ _ (wheelNextDueAudit_erases d j) (fun _ => preserves_pure _)

theorem sendOne_at :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit runOneSendWorkerAudit) := by
  apply audit_at _ _ runOneSendWorkerAudit_erases
  intro cs
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases x
  obtain ⟨holders,account⟩ := hi
  obtain ⟨pid,o,rest,_,post⟩ := Account.run_one_send w v account run
  exact ⟨holders.withoutSend rest,post⟩

theorem clearOne_at :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit runOneClearWorkerAudit) := by
  apply audit_at _ _ runOneClearWorkerAudit_erases
  intro cs
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases x
  obtain ⟨holders,account⟩ := hi
  obtain ⟨pid,o,rest,_,post⟩ := Account.run_one_clear w v account run
  exact ⟨holders.withoutClear rest,post⟩

private theorem step_at (bucket : UInt64) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  audit_at _ _ (requireStepCompleteAudit_erases bucket) (fun _ => stepComplete bucket)

theorem nothing_at (j : UInt64) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit (requireNothingDueAudit j)) :=
  audit_at _ _ (requireNothingDueAudit_erases j) (fun _ => nothingDue j)

theorem advance_at (ticks : Nat) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.audit (advanceAudit ticks)) :=
  audit_at _ _ (erasesPrefix_lift _) (fun _ => advance ticks)

private theorem drained_source (what : String) (queues : List Bool) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Env.requireDrained what queues) :=
  stored _ (requireDrained_sameKernel what queues)

private theorem idleDevice_source :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) Env.requireIdleDevice := by
  unfold Env.requireIdleDevice
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.requireNoCryptWork; exact stored _ requireNoCryptWork_sameKernel)
    | (allocation_release_lift_from WG.M
       exact stored _ (liftWG_sameProductStore getDev getDev_sameWGStore))
    | retired_timer_product_step

private theorem mixed_at (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erase : ErasesPrefix g a)
    (keeps : ∀ cs, Preserves (fun w : World => ExactBoundary cs loans w.wg) a) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) (RxHistory.mixed g) :=
  kept_at _ _ (RxHistory.mixed_erases erase) (Appends.focus _ _ _)
    (fun w h => focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent NapiCarrier.removed
      (fun _ => rfl) (auditFocus g) w h) keeps

/-- Every exact poll-free atom of the existing deferred source preserves this
account. Saved scans use their actual getter/erasure, with no invented funds. -/
theorem atoms : RxHistory.DeferredSource.AtomContracts
    (ExactAt initial loans before) (fun _ => True) (fun {_} g => g) := by
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
    (crypt : PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) (RxHistory.runTimers j) := by
  rw [RxHistory.DeferredSource.timers_factor]
  exact RxHistory.DeferredSource.timers_preserves (I := ExactAt initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => ExactAt.store hi same) _ atoms _ crypt j

/-- The placeholder retains the original crypt and send observers at their
source call positions; neither callback is assumed independent of history. -/
theorem runTimersPlaceholder (j : UInt64)
    (crypt : PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers)
    (send : PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      RxHistory.runSendWorkers) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor]
  exact RxHistory.DeferredSource.placeholder_preserves (I := ExactAt initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => ExactAt.store hi same) _ atoms _ crypt _ send j

theorem idleTimers
    (crypt : PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers)
    (send : PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      RxHistory.runSendWorkers) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact RxHistory.DeferredSource.idle_preserves (I := ExactAt initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => ExactAt.store hi same) _ atoms
    _ (fun j => runTimers j crypt) _ (fun j => runTimersPlaceholder j crypt send)

theorem afterAdvance
    (crypt : PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      RxHistory.runCryptWorkers)
    (send : PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      RxHistory.runSendWorkers) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact RxHistory.DeferredSource.afterAdvance_preserves (I := ExactAt initial loans before) (S := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => ExactAt.store hi same) _ atoms
    _ (fun j => runTimers j crypt) _ (fun j => runTimersPlaceholder j crypt send)

/-- The endpoint account is obtained from the same original execution and its
own appended removal suffix. This assertion says nothing about a Stop state. -/
theorem normal (g : RxHistory.Obs α) (a : Leanux.M α) (erase : ErasesPrefix g a)
    (keeps : PrefixPreserves (ExactAt cs loans h) (fun _ => True) g)
    (hi : ExactBoundary cs loans w.wg) (run : a.run w = .ok (result,v)) :
    let k := (runPrefix g w h).2
    ∃ suffix, k = h ++ suffix ∧
      ExactBoundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg := by
  have actual := (erase w h).trans run
  have post := (keeps w h (ExactAt.start hi h)).choose_spec.2.2
  simpa only [actual,ExactAt] using post

theorem runTimers_normal (j : UInt64) (h : List RxHistory.Event)
    (crypt : PrefixPreserves (ExactAt cs loans h) (fun _ => True) RxHistory.runCryptWorkers)
    (hi : ExactBoundary cs loans w.wg) (run : (Env.runTimers j).run w = .ok (result,v)) :
    let k := (runPrefix (RxHistory.runTimers j) w h).2
    ∃ suffix, k = h ++ suffix ∧
      ExactBoundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg :=
  normal _ _ (RxHistory.runTimers_erases j) (runTimers j crypt) hi run

theorem afterAdvance_normal (h : List RxHistory.Event)
    (crypt : PrefixPreserves (ExactAt cs loans h) (fun _ => True) RxHistory.runCryptWorkers)
    (send : PrefixPreserves (ExactAt cs loans h) (fun _ => True) RxHistory.runSendWorkers)
    (hi : ExactBoundary cs loans w.wg) (run : Env.afterAdvance.run w = .ok ((),v)) :
    let k := (runPrefix RxHistory.afterAdvance w h).2
    ∃ suffix, k = h ++ suffix ∧
      ExactBoundary (remaining cs (NapiCarrier.removedPackets suffix)) loans v.wg :=
  normal _ _ RxHistory.afterAdvance_erases (afterAdvance crypt send) hi run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.TimerEnvironment
