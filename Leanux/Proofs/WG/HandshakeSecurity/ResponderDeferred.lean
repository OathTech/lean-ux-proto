import Leanux.Proofs.WG.HandshakeSecurity.ResponderScheduler

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins CurrentEnvironment

private theorem store (a : Leanux.M α) (frame : SameProductStore a) :
    Joint.Preserves (liftPrefix a) := Joint.lift_store a frame

private theorem audit_store (a : Leanux.M α) (frame : SameProductStore a) :
    Joint.Preserves (RxHistory.audit (liftPrefix a)) :=
  Joint.from_global _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDeferred.«0».Leanux.Proofs.WG.PublicationDeferred.audit_store) a frame)
    (Global.audited _ _ (erasesPrefix_lift _) (native_product_store frame))

private theorem mixed_store (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (allocation : PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe g)
    (frame : SameProductStore a) : Joint.Preserves (RxHistory.mixed g) :=
  Joint.from_global _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDeferred.«0».Leanux.Proofs.WG.PublicationDeferred.mixed_store) g a erases allocation frame)
    (Global.mixed g a erases (native_product_store frame))

/-- Retain C1's exact saved-peer postcondition while transporting responder
chronology on the same execution and journal, including its failure prefix. -/
theorem join_ensures (g : RxHistory.Obs α) (P : World → Prop) (Q : α → World → Prop)
    (inherited : PrefixEnsures (fun h w => PublicationJoint.Inv h w ∧ P w)
      PublicationJoint.Safe g (fun x h w => PublicationJoint.Inv h w ∧ Q x w))
    (chronology : Global.Preserves g) :
    PrefixEnsures (fun h w => Joint.Inv h w ∧ P w) Joint.Safe g
      (fun x h w => Joint.Inv h w ∧ Q x w) := by
  intro w h hi
  obtain ⟨suffix, appends, priorSafe, priorPost⟩ := inherited w h ⟨hi.1.1,hi.2⟩
  obtain ⟨_,_,safe,post⟩ := chronology w h hi.1.2
  refine ⟨suffix,appends,⟨priorSafe,safe⟩,?_⟩
  cases run : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    rw [run] at priorPost post
    exact ⟨⟨priorPost.1,post⟩,priorPost.2⟩

private theorem drained (what : String) (queues : List Bool) :
    Joint.Preserves (RxHistory.mixed (requireDrainedPrefix what queues)) := by
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

macro "responder_deferred_steps " H1:term:max : tactic => `(tactic| first
  | (current_env_at Env.deliverSent; exact store _ deliverSent_sameKernel)
  | (current_env_at Env.requireNoCryptWork; exact store _ requireNoCryptWork_sameKernel)
  | (current_env_at getWG
     exact store _ (fun initial => productGetWG_spec (fun s => s = initial)))
  | (current_env_at modifyWG
     exact store _ (fun initial => productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (current_env_at RxHistory.audit; first | exact Joint.sendOne | exact Joint.clearOne $H1)
  | (current_env_at requireDrainedPrefix; exact drained _ _)
  | responder_env_steps $H1)

theorem runCryptWorkers (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.runCryptWorkers :=
  PrefixPreserves.bind (Joint.schedule H1 slots none) (fun _ => store _ deliverSent_sameKernel)

theorem runSendWorkers (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.runSendWorkers := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.runSendWorkers
  repeat' first
    | (current_env_at RxHistory.schedule; exact Joint.schedule H1 slots _)
    | responder_deferred_steps H1

theorem afterXmit (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.afterXmit := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.afterXmit
  repeat' first
    | (current_env_at RxHistory.runCryptWorkers; exact runCryptWorkers H1 slots)
    | (current_env_at RxHistory.runSendWorkers; exact runSendWorkers H1 slots)
    | responder_deferred_steps H1

private theorem saved_spec :
    PrefixEnsures Joint.Inv Joint.Safe (RxHistory.audit getDevSavedAudit)
      (fun d h w => Joint.Inv h w ∧ SavedPeers d.peers.toList (identityView w.wg)) := by
  apply PrefixEnsures.consequence (P := fun h w => Joint.Inv h w ∧ True)
    (Q := fun d h w => Joint.Inv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
  · apply join_ensures
    · exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDeferred.«0».Leanux.Proofs.WG.PublicationDeferred.saved_spec).consequence
        (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)
    · exact Global.audited _ _ getDevSavedAudit_erases (fun confirmed =>
        AuditedFrames.dev confirmed)
  · exact fun _ _ hi => ⟨hi,trivial⟩
  · exact fun _ _ _ hi => hi

private theorem saved : Joint.Preserves (RxHistory.audit getDevSavedAudit) :=
  (saved_spec.consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi.1)).preserves

private theorem wheel_spec (d : Device) (j : UInt64) : PrefixEnsures
    (fun h w => Joint.Inv h w ∧ SavedPeers d.peers.toList (identityView w.wg))
    Joint.Safe (RxHistory.audit (wheelNextDueAudit d j)) (fun _ => Joint.Inv) := by
  apply PrefixEnsures.consequence (Q := fun _ h w => Joint.Inv h w ∧ True)
  · apply join_ensures
    · exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationDeferred.«0».Leanux.Proofs.WG.PublicationDeferred.wheel_spec) d j).consequence
        (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi,trivial⟩)
    · exact Global.audited _ _ (wheelNextDueAudit_erases d j)
        (fun _ => preserves_pure _)
  · exact fun _ _ hi => hi
  · exact fun _ _ _ hi => hi.1

macro "responder_timer_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence (P := Joint.Inv) (Q := fun _ => Joint.Inv) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "responder_timer_calls " H1:term:max slots:term:max : tactic => `(tactic|
  first
  | (rx_timer_head timerDispatchAudit; exact Joint.timerDispatch _ _ _ _ _)
  | (rx_timer_head requireStepCompleteAudit; exact Joint.stepComplete _)
  | (rx_timer_head requireNothingDueAudit; exact Joint.nothingDue _)
  | (rx_timer_head placeholderTimerPassAudit; exact Joint.placeholderPass _)
  | (rx_timer_head runOneSendWorkerAudit; exact Joint.sendOne)
  | (rx_timer_head runOneClearWorkerAudit; exact Joint.clearOne $H1)
  | (rx_timer_head runCryptWorkers; exact runCryptWorkers $H1 $slots)
  | (rx_timer_head runSendWorkers; exact runSendWorkers $H1 $slots)
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
      (I := fun _ h w => Joint.Inv h w) (hs := fun _ _ _ hi => hi.safe)))

theorem runTimers (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (jHi : UInt64) : Joint.Preserves (RxHistory.runTimers jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (responder_timer_drop_saved; apply PrefixEnsures.bind saved_spec)
        | apply PrefixEnsures.bind saved_spec)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel_spec _ _))
    | (responder_timer_drop_saved; responder_timer_calls H1 slots)
    | responder_timer_calls H1 slots
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => Joint.Inv h w))
    | (responder_timer_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (responder_timer_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

theorem runTimersPlaceholder (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (jHi : UInt64) :
    Joint.Preserves (RxHistory.runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (rx_timer_head RxHistory.runTimers; exact runTimers H1 slots _)
    | (rx_timer_head getDevSavedAudit; exact saved)
    | responder_timer_calls H1 slots
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => Joint.Inv h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

macro "responder_deferred_timer_steps " H1:term:max : tactic => `(tactic| first
  | (environment_at "runOneSendWorkerAudit"; exact Joint.sendOne)
  | (environment_at "runOneClearWorkerAudit"; exact Joint.clearOne $H1)
  | (environment_at "placeholderTimerPassAudit"; exact Joint.placeholderPass _)
  | (environment_at "timerDispatchAudit"; exact Joint.timerDispatch _ _ _ _ _)
  | (environment_at "requireStepCompleteAudit"; exact Joint.stepComplete _)
  | (environment_at "requireNothingDueAudit"; exact Joint.nothingDue _)
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
  | responder_deferred_steps $H1)

theorem idleTimers (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.idleTimers := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.idleTimers
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact runTimers H1 slots _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder H1 slots _)
    | responder_deferred_timer_steps H1

theorem afterAdvance (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.afterAdvance := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.afterAdvance
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact runTimers H1 slots _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder H1 slots _)
    | responder_deferred_timer_steps H1

private theorem idleDevice : Joint.Preserves (RxHistory.mixed requireIdleDevicePrefix) := by
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
theorem deferred (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (call : EnvDeferredCall) : Joint.Preserves (RxHistory.deferred call) := by
  cases call with
  | drained what queues => exact drained what queues
  | idleDevice => exact idleDevice
  | noCrypt => exact audit_store _ requireNoCryptWork_sameKernel
  | crypt => exact runCryptWorkers H1 slots
  | sendOne => exact Joint.sendOne
  | clearOne => exact Joint.clearOne H1
  | sendAll => exact runSendWorkers H1 slots
  | afterXmit => exact afterXmit H1 slots
  | timerWorker timer => exact audit_store _ (timerWorker_sameKernel timer)
  | timers j => exact runTimers H1 slots j
  | placeholder j => exact runTimersPlaceholder H1 slots j
  | idle => exact idleTimers H1 slots
  | advance ticks => exact audit_store _ (advance_sameKernel ticks)
  | afterAdvance => exact afterAdvance H1 slots


end Leanux.Proofs.WG.HandshakeSecurity.Responder.Deferred
