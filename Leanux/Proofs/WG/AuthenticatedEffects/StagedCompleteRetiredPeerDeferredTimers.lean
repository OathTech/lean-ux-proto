import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferred
import Leanux.Proofs.WG.Queues.HolderAuxTimers

/-! Paired exact-account timer composition retains the real saved getter
and its conditional wheel scan. The scheduler obligations remain explicit;
all timer and selected send/clear work callbacks are concrete. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.DeferredTimers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits DurableHolders Auxiliary
variable {initial : Ledger} {loans : Reservations} {before : List RxHistory.Event}

private theorem store (a : Leanux.M α) (frame : SameProductStore a) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe)
    (fun _ _ _ same hi => Auxiliary.store hi same) frame

private theorem clearOne : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit runOneClearWorkerAudit) :=
  pair_preserves _
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.clearOne)
    TimerEnvironment.clearOne_at

private theorem saved_spec : PrefixEnsures (Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit getDevSavedAudit)
    (fun d h w => Inv initial loans before h w ∧ SavedPeers d.peers.toList (identityView w.wg)) := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.saved_spec) w h hi.1
  have exactPost := (TimerEnvironment.atoms.saved w h hi.2).choose_spec.2.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit getDevSavedAudit) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post exactPost
    exact ⟨⟨post.1,exactPost⟩,post.2⟩

private theorem saved : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
    (RxHistory.audit getDevSavedAudit) :=
  (saved_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)).preserves

private theorem wheel_spec (d : Device) (j : UInt64) : PrefixEnsures
    (fun h w => Inv initial loans before h w ∧ SavedPeers d.peers.toList (identityView w.wg))
    OwnerChecks.Safe (RxHistory.audit (wheelNextDueAudit d j))
    (fun _ => Inv initial loans before) := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.wheel_spec)
      d j w h ⟨hi.1.1,hi.2⟩
  have exactPost := (TimerEnvironment.atoms.wheel d j w h hi.1.2).choose_spec.2.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit (wheelNextDueAudit d j)) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post exactPost
    exact ⟨post,exactPost⟩

private theorem stepComplete (bucket : UInt64) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  pair_preserves _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.stepComplete) bucket)
    (TimerEnvironment.atoms.stepComplete bucket)

private theorem nothingDue (j : UInt64) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (requireNothingDueAudit j)) :=
  pair_preserves _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.nothingDue) j)
    (TimerEnvironment.nothing_at j)

private theorem timerDispatch (kind : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (prior : Option UInt64) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (timerDispatchAudit kind pid timer entry prior)) :=
  pair_preserves _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.timerDispatch) kind pid timer entry prior)
    (TimerEnvironment.dispatch_at kind pid timer entry prior)

private theorem placeholderPass (j : UInt64) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  pair_preserves _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.placeholderPass) j)
    (TimerEnvironment.placeholderPass_at j)

macro "exact_aux_timer_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence
    (P := Inv _ _ _) (Q := fun _ => Inv _ _ _) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "exact_aux_timer_calls" actors:term : tactic => `(tactic| first
  | (rx_timer_head timerDispatchAudit; exact timerDispatch _ _ _ _ _)
  | (rx_timer_head requireStepCompleteAudit; exact stepComplete _)
  | (rx_timer_head requireNothingDueAudit; exact nothingDue _)
  | (rx_timer_head placeholderTimerPassAudit; exact placeholderPass _)
  | (rx_timer_head runOneSendWorkerAudit; exact Deferred.sendOne)
  | (rx_timer_head runOneClearWorkerAudit; exact clearOne)
  | (rx_timer_head RxHistory.runCryptWorkers; exact Deferred.crypt $actors)
  | (rx_timer_head RxHistory.runSendWorkers; exact Deferred.runSendWorkers $actors)
  | (rx_timer_head getWG; exact store _ (fun initial => productGetWG_spec (fun s => s=initial)))
  | (rx_timer_head modifyWG; exact store _ (fun initial => productModifyWG_spec (fun s => s=initial) _ (fun _ => rfl)))
  | (rx_timer_head getEnv; exact store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl))
  | (rx_timer_head Env.peekNextSite; exact store _ peekNextSite_sameKernel)
  | (rx_timer_head Env.deliverSent; exact store _ deliverSent_sameKernel)
  | (rx_timer_head throw; exact store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run))
  | (audit_contract_head liftPrefix; exact store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (rx_timer_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
  | (rx_timer_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => Inv _ _ _ h w) (hs := fun _ _ _ hi => hi.safe)))

/-- The exact saved getter precedes each wheel scan. Source dispatch, cleanup,
crypt work and stopping guards remain in the original record-driven loop. -/
theorem runTimers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (actors : Scheduler.Actors initial loans before) (jHi : UInt64) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.runTimers jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (exact_aux_timer_drop_saved; apply PrefixEnsures.bind saved_spec)
        | apply PrefixEnsures.bind saved_spec)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel_spec _ _))
    | (exact_aux_timer_drop_saved; exact_aux_timer_calls actors)
    | exact_aux_timer_calls actors
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => Inv initial loans before h w))
    | (exact_aux_timer_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (exact_aux_timer_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimersPlaceholder (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (actors : Scheduler.Actors initial loans before) (jHi : UInt64) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (rx_timer_head RxHistory.runTimers; exact runTimers _ _ _ actors _)
    | (rx_timer_head getDevSavedAudit; exact saved)
    | exact_aux_timer_calls actors
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => Inv initial loans before h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

/-- Both record-driven and placeholder paths use the actual source clocks,
with the original end-of-wait check and no new timing assumption. -/
theorem idleTimers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (actors : Scheduler.Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.idleTimers := by
  have safe : ∀ h w, Inv initial loans before h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      Inv initial loans before h w → Inv initial loans before h v :=
    fun _ _ _ same hi => Auxiliary.store hi same
  unfold RxHistory.idleTimers
  repeat' first
    | (scheduler_preserve_at RxHistory.runTimers; exact runTimers _ _ _ actors _)
    | (scheduler_preserve_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _ _ _ actors _)
    | (scheduler_preserve_at requireNothingDueAudit; exact nothingDue _)
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves _ _ (RxHistory.runTimers _ >>= fun _ => pure ())
       exact PrefixPreserves.bind (runTimers _ _ _ actors _) (fun _ => PrefixPreserves.pure safe ()))
    | deferred_raw_steps safe saved

theorem afterAdvance (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (actors : Scheduler.Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.afterAdvance := by
  have safe : ∀ h w, Inv initial loans before h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      Inv initial loans before h w → Inv initial loans before h v :=
    fun _ _ _ same hi => Auxiliary.store hi same
  unfold RxHistory.afterAdvance
  repeat' first
    | (scheduler_preserve_at RxHistory.runTimers; exact runTimers _ _ _ actors _)
    | (scheduler_preserve_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _ _ _ actors _)
    | (scheduler_preserve_at requireNothingDueAudit; exact nothingDue _)
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves _ _ (RxHistory.runTimers _ >>= fun _ => pure ())
       exact PrefixPreserves.bind (runTimers _ _ _ actors _) (fun _ => PrefixPreserves.pure safe ()))
    | deferred_raw_steps safe saved

/-- All actual deferred constructors preserve the paired invariant. No
unconditional wheel-owner contract or independent history is introduced. -/
theorem deferred (actors : Scheduler.Actors initial loans before) (call : EnvDeferredCall) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.deferred call) := by
  cases call with
  | drained what flags => exact Deferred.drained what flags
  | idleDevice => exact pair_preserves _ (HolderAuxTimers.deferred initial loans before .idleDevice) TimerEnvironment.atoms.idleDevice
  | noCrypt => exact pair_preserves _ (HolderAuxTimers.deferred initial loans before .noCrypt) TimerEnvironment.atoms.noCrypt
  | crypt => exact Deferred.crypt actors
  | sendOne => exact Deferred.sendOne
  | clearOne => exact clearOne
  | sendAll => exact Deferred.runSendWorkers actors
  | afterXmit => exact Deferred.afterXmit actors
  | timerWorker timer => exact pair_preserves _ (HolderAuxTimers.deferred initial loans before (.timerWorker timer)) (TimerEnvironment.atoms.timerWorker timer)
  | timers j => exact runTimers initial loans before actors j
  | placeholder j => exact runTimersPlaceholder initial loans before actors j
  | idle => exact idleTimers initial loans before actors
  | advance ticks => exact pair_preserves _ (HolderAuxTimers.deferred initial loans before (.advance ticks)) (TimerEnvironment.advance_at ticks)
  | afterAdvance => exact afterAdvance initial loans before actors

/-- A native return determines its original observer suffix and both account
components at the same endpoint. The theorem makes no stopped-state claim. -/
theorem deferred_normal (actors : Scheduler.Actors initial loans before)
    (call : EnvDeferredCall) {result : call.Result} (hi : Inv initial loans before h w)
    (run : call.original.run w=.ok (result,v)) :
    Inv initial loans before (runPrefix (RxHistory.deferred call) w h).2 v :=
  Deferred.normal _ _ (RxHistory.deferred_erases call) (deferred actors call) hi run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.DeferredTimers
