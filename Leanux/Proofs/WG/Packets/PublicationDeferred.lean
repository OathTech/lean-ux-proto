import Leanux.Proofs.WG.Packets.PublicationAudited
import Leanux.Proofs.WG.Packets.PublicationEnvironment

/-! The original deferred observers retain owner evidence and packet certificates.
Saved-peer scans retain the exact getter receipt; scheduler calls may extend
publication history, so the full loop is composed on its actual journal. -/
namespace Leanux.Proofs.WG.PublicationDeferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins CurrentEnvironment
open Origins.HistorySupport (sensitive)

private theorem store (a : Leanux.M α) (frame : SameProductStore a) :
    PublicationJoint.Preserves (liftPrefix a) := PublicationJoint.lift_store a frame

private theorem audit_store (a : Leanux.M α) (frame : SameProductStore a) :
    PublicationJoint.Preserves (RxHistory.audit (liftPrefix a)) :=
  (FocusedInvariant.lift RxHistory.Event.audit RxHistory.auditEvent a (store a frame)).2

private theorem mixed_store (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (allocation : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe g)
    (frame : SameProductStore a) : PublicationJoint.Preserves (RxHistory.mixed g) :=
  PublicationJoint.mixed_store g a
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.mixed_store)
      g a erases allocation frame) erases frame

theorem sendOne : PublicationJoint.Preserves (RxHistory.audit runOneSendWorkerAudit) :=
  PublicationAudited.sendOne

theorem clearOne : PublicationJoint.Preserves (RxHistory.audit runOneClearWorkerAudit) :=
  PublicationAudited.clearOne

private theorem drained (what : String) (queues : List Bool) :
    PublicationJoint.Preserves (RxHistory.mixed (requireDrainedPrefix what queues)) := by
  apply mixed_store _ _ (requireDrainedPrefix_erases _ _) (requireDrainedPrefix_allocation what queues)
  have tail : SameProductStore (do
      let d ← (liftWG getDev : Leanux.M Device)
      if d.peers.toList.any (fun x => x.2.napiScheduled) then
        invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)") := by
    apply SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore)
    intro d
    split
    · intro initial; exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi)
    · exact SameView.pure _ _
  unfold Env.requireDrained
  by_cases h : queues.any id = true <;> simp only [h,↓reduceIte]
  · exact SameView.bind (fun initial => productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi)) (fun _ => tail)
  · exact tail

macro "publication_deferred_steps" : tactic => `(tactic| first
  | (current_env_at Env.deliverSent; exact store _ deliverSent_sameKernel)
  | (current_env_at Env.requireNoCryptWork; exact store _ requireNoCryptWork_sameKernel)
  | (current_env_at getWG
     exact store _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (current_env_at modifyWG
     exact store _ (fun initial => productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (current_env_at RxHistory.audit; first | exact sendOne | exact clearOne)
  | (current_env_at requireDrainedPrefix; exact drained _ _)
  | publication_env_steps)

theorem runCryptWorkers : PublicationJoint.Preserves RxHistory.runCryptWorkers :=
  PrefixPreserves.bind (PublicationJoint.schedule none) (fun _ => store _ deliverSent_sameKernel)

theorem runSendWorkers : PublicationJoint.Preserves RxHistory.runSendWorkers := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.runSendWorkers
  repeat' first
    | (current_env_at RxHistory.schedule; exact PublicationJoint.schedule _)
    | publication_deferred_steps

theorem afterXmit : PublicationJoint.Preserves RxHistory.afterXmit := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.afterXmit
  repeat' first
    | (current_env_at RxHistory.runCryptWorkers; exact runCryptWorkers)
    | (current_env_at RxHistory.runSendWorkers; exact runSendWorkers)
    | publication_deferred_steps

private theorem saved_spec :
    PrefixEnsures PublicationJoint.Inv PublicationJoint.Safe (RxHistory.audit getDevSavedAudit)
      (fun d h w => PublicationJoint.Inv h w ∧ SavedPeers d.peers.toList (identityView w.wg)) := by
  apply PrefixEnsures.consequence (P := fun h w => PublicationJoint.Inv h w ∧ True)
    (Q := fun d h w => PublicationJoint.Inv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
  · apply PublicationAudited.join_ensures
    · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.saved_spec).consequence
        (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)
    · exact PublicationAudited.saved
  · exact fun _ _ hi => ⟨hi,trivial⟩
  · exact fun _ _ _ hi => hi

private theorem saved : PublicationJoint.Preserves (RxHistory.audit getDevSavedAudit) :=
  (saved_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)).preserves

private theorem wheel_spec (d : Device) (j : UInt64) : PrefixEnsures
    (fun h w => PublicationJoint.Inv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
    PublicationJoint.Safe (RxHistory.audit (wheelNextDueAudit d j)) (fun _ => PublicationJoint.Inv) := by
  apply PrefixEnsures.consequence
    (Q := fun _ h w => PublicationJoint.Inv h w ∧ True)
  · apply PublicationAudited.join_ensures
    · exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.wheel_spec) d j).consequence
        (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi,trivial⟩)
    · exact PublicationAudited.wheel d j
  · exact fun _ _ hi => hi
  · exact fun _ _ _ hi => hi.1

private theorem stepComplete (b : UInt64) :
    PublicationJoint.Preserves (RxHistory.audit (requireStepCompleteAudit b)) := PublicationAudited.stepComplete b

private theorem nothingDue (j : UInt64) :
    PublicationJoint.Preserves (RxHistory.audit (requireNothingDueAudit j)) := PublicationAudited.nothingDue j

private theorem timerDispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    PublicationJoint.Preserves (RxHistory.audit (timerDispatchAudit worker pid timer we step)) :=
  PublicationAudited.timerDispatch worker pid timer we step

private theorem placeholderPass (j : UInt64) :
    PublicationJoint.Preserves (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  PublicationAudited.placeholderPass j

macro "publication_timer_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence (P := PublicationJoint.Inv) (Q := fun _ => PublicationJoint.Inv) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "publication_timer_calls" : tactic => `(tactic|
  first
  | (rx_timer_head timerDispatchAudit; exact timerDispatch _ _ _ _ _)
  | (rx_timer_head requireStepCompleteAudit; exact stepComplete _)
  | (rx_timer_head requireNothingDueAudit; exact nothingDue _)
  | (rx_timer_head placeholderTimerPassAudit; exact placeholderPass _)
  | (rx_timer_head runOneSendWorkerAudit; exact sendOne)
  | (rx_timer_head runOneClearWorkerAudit; exact clearOne)
  | (rx_timer_head runCryptWorkers; exact runCryptWorkers)
  | (rx_timer_head runSendWorkers; exact runSendWorkers)
  | (rx_timer_head getWG; exact store _ (by
      intro initial; exact productGetWG_spec (fun s => s = initial)))
  | (rx_timer_head modifyWG; exact store _ (by
      intro initial; exact productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_timer_head getEnv; exact store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (rx_timer_head Env.peekNextSite; exact store _ peekNextSite_sameKernel)
  | (rx_timer_head Env.deliverSent; exact store _ deliverSent_sameKernel)
  | (rx_timer_head throw; exact store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      cases hr))
  | (audit_contract_head liftPrefix; exact store _ (by
      intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (rx_timer_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
  | (rx_timer_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => PublicationJoint.Inv h w) (hs := fun _ _ _ hi => hi.safe)))

theorem runTimers (jHi : UInt64) : PublicationJoint.Preserves (RxHistory.runTimers jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (publication_timer_drop_saved; apply PrefixEnsures.bind saved_spec)
        | apply PrefixEnsures.bind saved_spec)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel_spec _ _))
    | (publication_timer_drop_saved; publication_timer_calls)
    | publication_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => PublicationJoint.Inv h w))
    | (publication_timer_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (publication_timer_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimersPlaceholder (jHi : UInt64) :
    PublicationJoint.Preserves (RxHistory.runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (rx_timer_head RxHistory.runTimers; exact runTimers _)
    | (rx_timer_head getDevSavedAudit; exact saved)
    | publication_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => PublicationJoint.Inv h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

macro "publication_deferred_timer_steps" : tactic => `(tactic| first
  | (environment_at "runOneSendWorkerAudit"; exact sendOne)
  | (environment_at "runOneClearWorkerAudit"; exact clearOne)
  | (environment_at "placeholderTimerPassAudit"; exact placeholderPass _)
  | (environment_at "timerDispatchAudit"; exact timerDispatch _ _ _ _ _)
  | (environment_at "requireStepCompleteAudit"; exact stepComplete _)
  | (environment_at "requireNothingDueAudit"; exact nothingDue _)
  | (environment_at "getDevSavedAudit"; exact saved)
  | (current_env_at peekSiteU64
     exact store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at hiddenJiffies
     exact store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at getEnv
     exact store _ (by
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w x v hr
       cases hr
       rfl))
  | (current_env_at throw; exact store _ (HistorySupport.source_throw _ _))
  | (current_env_at Env.peekNextSite; exact store _ peekNextSite_sameKernel)
  | (current_env_at Env.timerWorker; exact store _ (timerWorker_sameKernel _))
  | environment_reduce
  | environment_join
  | environment_join_use
  | publication_deferred_steps)

theorem idleTimers : PublicationJoint.Preserves RxHistory.idleTimers := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.idleTimers
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact runTimers _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _)
    | publication_deferred_timer_steps

theorem afterAdvance : PublicationJoint.Preserves RxHistory.afterAdvance := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.afterAdvance
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact runTimers _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder _)
    | publication_deferred_timer_steps

private theorem idleDevice : PublicationJoint.Preserves (RxHistory.mixed requireIdleDevicePrefix) := by
  apply mixed_store _ _ requireIdleDevicePrefix_erases requireIdleDevicePrefix_allocation
  unfold Env.requireIdleDevice
  apply SameView.bind requireNoCryptWork_sameKernel
  intro _
  apply SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore)
  intro d
  split
  · intro initial; exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi)
  · exact SameView.pure _ _

/-- All fourteen actual deferred-call constructors retain positional checks,
including records emitted before a Stop. Incoming journals remain arbitrary. -/
theorem deferred (call : EnvDeferredCall) : PublicationJoint.Preserves (RxHistory.deferred call) := by
  cases call with
  | drained what queues => exact drained what queues
  | idleDevice => exact idleDevice
  | noCrypt => exact audit_store _ requireNoCryptWork_sameKernel
  | crypt => exact runCryptWorkers
  | sendOne => exact sendOne
  | clearOne => exact clearOne
  | sendAll => exact runSendWorkers
  | afterXmit => exact afterXmit
  | timerWorker timer => exact audit_store _ (timerWorker_sameKernel timer)
  | timers j => exact runTimers j
  | placeholder j => exact runTimersPlaceholder j
  | idle => exact idleTimers
  | advance ticks => exact audit_store _ (advance_sameKernel ticks)
  | afterAdvance => exact afterAdvance


end Leanux.Proofs.WG.PublicationDeferred
