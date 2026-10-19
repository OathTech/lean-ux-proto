import Leanux.Proofs.WG.Queues.PollFatePromotion
import Leanux.Proofs.WG.Origins.OwnerSyscalls
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

/-! Allocation is captured at the actual poll entry. This strengthens the
positional certificate separately; only normal return restores certificates
for every removal. Stopped outcomes retain the existing owner-safe journal. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.PollReleaseCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- A selected global removal position belongs to this particular completed
local poll. Its entire promoted suffix is already in the returned journal. -/
def Certificate (cut : List RxHistory.Event) (n skb : Nat) (stamp : PacketStamp)
    (history : List RxHistory.Event) : Prop :=
  ∃ incoming w pid budget result v before after tail,
    cut=incoming++before.map RxHistory.promote ∧
    AllocationInv (RxHistory.prior incoming) w.wg ∧
    runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior incoming))=
      (.ok (result,v),RxJoint.seed (RxHistory.prior incoming)++
        (before++RxJoint.Event.removed n skb stamp::after)) ∧
    history=incoming++(before++RxJoint.Event.removed n skb stamp::after).map RxHistory.promote++tail

def EventCertificate (cut : List RxHistory.Event) (event : RxHistory.Event)
    (history : List RxHistory.Event) : Prop :=
  match event with
  | .removed n skb stamp=>Certificate cut n skb stamp history
  | _=>True

/-- The incoming journal is arbitrary; only new exact positions are certified. -/
def Certificates (base history : List RxHistory.Event) : Prop :=
  ∃suffix,history=base++suffix ∧ ∀pre event post,suffix=pre++event::post→
    EventCertificate (base++pre) event history

def Inv (base h : List RxHistory.Event) (w : World) : Prop :=
  OwnerChecks.Inv h w ∧ Certificates base h

abbrev Preserves (base : List RxHistory.Event) (action : RxHistory.Obs α) :=
  PrefixPreserves (Inv base) OwnerChecks.Safe action

theorem initial (base : List RxHistory.Event) : Certificates base base := by
  refine ⟨[],by simp,?_⟩
  intro pre event post impossible
  cases pre <;> cases impossible

theorem Certificate.append (hi : Certificate cut n skb stamp h) (suffix : List RxHistory.Event) :
    Certificate cut n skb stamp (h++suffix) := by
  obtain ⟨incoming,w,pid,budget,result,v,before,after,tail,position,allocation,run,hist⟩ := hi
  exact ⟨incoming,w,pid,budget,result,v,before,after,tail++suffix,position,allocation,run,
    by rw [hist,List.append_assoc]⟩

theorem EventCertificate.append (hi : EventCertificate cut event h) (suffix : List RxHistory.Event) :
    EventCertificate cut event (h++suffix) := by
  cases event <;> first | trivial | exact Certificate.append hi suffix

theorem append (hi : Certificates base h) (suffix : List RxHistory.Event)
    (fresh : ∀pre event post,suffix=pre++event::post→EventCertificate (h++pre) event (h++suffix)) :
    Certificates base (h++suffix) := by
  obtain ⟨old,hist,checked⟩ := hi
  refine ⟨old++suffix,by rw [hist,List.append_assoc],?_⟩
  apply (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (fun pre event=>EventCertificate (base++pre) event (h++suffix)) old suffix
  · intro pre event post position
    exact (checked pre event post position).append suffix
  · intro pre event post position
    simpa only [←List.append_assoc,←hist] using fresh pre event post position

private theorem metadata_quiet (action : RxHistory.Obs α) (appends : Appends action)
    (frame : HistoryFrame PollFatePromotion.removed action) :
    PrefixPreserves (fun h (_ : World)=>Certificates base h) (fun _=>True) action := by
  intro w h hi
  obtain ⟨suffix,hist⟩ := appends w h
  have emptySuffix : suffix.filterMap PollFatePromotion.removed=[] := by
    have same := frame w h
    rw [hist,List.filterMap_append] at same
    exact List.append_cancel_left (by simpa only [List.append_nil] using same)
  have kept : Certificates base (h++suffix) := append hi suffix (by
    intro pre event post position
    have noEvent : PollFatePromotion.removed event=none := by
      have empty := emptySuffix
      rw [position,List.filterMap_append,List.filterMap_cons] at empty
      cases he : PollFatePromotion.removed event <;> simp_all
    cases event <;> first | trivial | cases noEvent)
  refine ⟨suffix,hist,True.intro,?_⟩
  cases run:(runPrefix action w h).1 with
  | error reason=>trivial
  | ok out=>simpa only [hist] using kept

/-- Extra saved-source predicates are retained, rather than replaced with an
unconditional scan contract. Both proofs concern the identical execution. -/
theorem quiet_ensures (action : RxHistory.Obs α) (appends : Appends action)
    (frame : HistoryFrame PollFatePromotion.removed action)
    (spec : PrefixEnsures P S action Q) :
    PrefixEnsures (fun h w=>P h w ∧ Certificates base h) S action
      (fun x h w=>Q x h w ∧ Certificates base h) := by
  intro w h hi
  obtain ⟨suffix,hist,hs,post⟩ := spec w h hi.1
  obtain ⟨_,_,_,metadata⟩ := metadata_quiet action appends frame w h hi.2
  refine ⟨suffix,hist,hs,?_⟩
  cases run:(runPrefix action w h).1 with
  | error reason=>trivial
  | ok out=>exact ⟨by simpa only [run] using post,by simpa only [run] using metadata⟩

theorem quiet (action : RxHistory.Obs α) (appends : Appends action)
    (frame : HistoryFrame PollFatePromotion.removed action) (owner : OwnerChecks.Preserves action) :
    Preserves base action := quiet_ensures action appends frame owner

theorem lift (action : Leanux.M α) (owner : OwnerChecks.Preserves (liftPrefix action)) :
    Preserves base (liftPrefix action) := quiet _ (Appends.lift _) (HistoryFrame.lift _ _) owner

theorem raw (action : Leanux.M α) (frame : SameProductStore action) : Preserves base (liftPrefix action) :=
  lift action (OwnerControlCalls.lift_store action frame)

theorem audit (action : AuditM α) (owner : OwnerChecks.Preserves (RxHistory.audit action)) :
    Preserves base (RxHistory.audit action) :=
  quiet _ (Appends.focus _ _ _) (fun w h=>
    focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent PollFatePromotion.removed (fun _=>rfl) action w h) owner

theorem mixed (action : PrefixM LifetimeEvent α) (owner : OwnerChecks.Preserves (RxHistory.mixed action)) :
    Preserves base (RxHistory.mixed action) := audit _ owner

theorem origin (action : PrefixM Origins.Event α)
    (owner : OwnerChecks.Preserves (Origins.HistoryAdapters.focus action)) :
    Preserves base (Origins.HistoryAdapters.focus action) :=
  quiet _ (Appends.focus _ _ _)
    (Origins.HistoryAdapters.focus_other PollFatePromotion.removed (by intro e;cases e <;> rfl) action) owner

private theorem filterMap_some {A B : Type} (f : A→B) (xs : List A) :
    xs.filterMap (fun x=>some (f x))=xs.map f :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.PollFatePromotion.«0».Leanux.Proofs.WG.Queues.RxCredits.PollFatePromotion.filterMap_some) f xs

/-- The allocation invariant belongs to the same incoming World and journal
used to execute this particular poll. -/
theorem poll (pid : PeerId) (budget : Nat) : Preserves base (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨_,_,hs,owner⟩ := OwnerWorkers.poll pid budget w h hi.1
  obtain ⟨suffix,localHist⟩ := RxJoint.poll_appends pid budget w (RxJoint.seed (RxHistory.prior h))
  have observed := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl localHist)
  refine ⟨suffix.map RxHistory.promote,by rw [observed],hs,?_⟩
  rw [observed] at owner ⊢
  cases actual:(runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).1 with
  | error reason=>trivial
  | ok out=>
    refine ⟨by simpa only [actual] using owner,?_⟩
    apply append hi.2
    intro pre event post position
    cases event <;> try trivial
    case removed n skb stamp=>
      obtain ⟨before,e,after,hist,hbefore,he,hafter⟩ :=
        RxLink.filterMap_position (fun e=>some (RxHistory.promote e)) suffix pre (.removed n skb stamp) post
          (by simpa only [filterMap_some] using position)
      have value : e=RxJoint.Event.removed n skb stamp := by cases e <;> cases he <;> rfl
      subst e
      refine ⟨h,w,pid,budget,out.1,out.2,before,after,[],?_,hi.1.allocation,?_,?_⟩
      · simpa only [filterMap_some] using congrArg (h++·) hbefore.symm
      · exact Prod.ext actual (by rw [localHist,hist])
      · simp only [hist,List.append_nil]

private theorem safe : ∀ h w,Inv base h w→OwnerChecks.Safe h := fun _ _ hi=>hi.1.safe
private theorem store : ∀ h (w v : World),productStoreView v=productStoreView w→Inv base h w→Inv base h v :=
  fun h w v eq hi=>⟨OwnerWorkers.store h w v eq hi.1,hi.2⟩

theorem softirq : Preserves base RxHistory.napiSoftirq := by
  rw [NapiSource.softirq_factor]
  exact RxNapi.softirq_preserves safe store (mixed _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerWorkers.«0».Leanux.Proofs.WG.OwnerWorkers.pending)) poll

theorem inline : Preserves base RxHistory.pollScheduledInline := by
  rw [NapiSource.inline_factor]
  exact RxNapi.inline_preserves safe store (mixed _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerWorkers.«0».Leanux.Proofs.WG.OwnerWorkers.pending)) poll

theorem irqExit : Preserves base RxHistory.napiIrqExit := by
  rw [NapiSource.irqExit_factor]
  exact RxNapi.irqExit_preserves safe store (mixed _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerWorkers.«0».Leanux.Proofs.WG.OwnerWorkers.scheduled)) softirq

theorem decrypt : Preserves base RxHistory.decryptStep := by
  rw [NapiSource.decrypt_factor]
  exact NapiSource.decrypt_preserves safe (origin _ OwnerPrepare.prepare) (fun pid=>mixed _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCryptWorkers.«0».Leanux.Proofs.WG.OwnerCryptWorkers.pay) pid)) softirq irqExit

theorem decryptIteration : Preserves base RxHistory.decryptIteration := by
  rw [NapiSource.decryptIteration_factor]
  apply workerIterPrefix_preserves _ _ safe decrypt
  exact PrefixPreserves.bind (raw _ (condResched_sameKernel _)) (fun b=>
    raw _ (fun initial=>productAmbient_spec (AmbientM.branch .decWorkerNeedResched b) _ (fun _ _ hi=>hi)))

theorem receiveIteration : Preserves base Origins.HistoryAdapters.receiveIteration :=
  workerIterPrefix_preserves _ _ safe (origin _ OwnerHandshake.receiveStep) (raw _ (condResched_sameKernel _))

theorem encryptIteration : Preserves base RxHistory.encryptIteration :=
  PrefixPreserves.bind (mixed _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.poll)) (fun item=>
    PrefixPreserves.bind softirq (fun _=>mixed _
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.tail) item)))

private theorem schedulerAtoms : RxHistory.SchedulerSource.AtomContracts
    (Inv base) OwnerChecks.Safe (fun {_} a=>a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro α a
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.mixed_lift)
      _ (fun initial=>productAmbient_spec a _ (fun _ _ hi=>hi)))
  · intro α e
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.mixed_throw) e)
  · intro pid
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.peer) pid)
  · intro id
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.packet) id)
  · intro f
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.work) f)
  · intro a
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.occupancy) a)
  · exact mixed _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.refills)
  · intro next
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.pending) next)
  · intro a
    exact mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.hasWork) a)
  · exact audit _ OwnerChecks.filter_probe
theorem cryptAhead (pid : PeerId) : Preserves base (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves safe _ schedulerAtoms _ encryptIteration pid

theorem activationIteration (a : Activation) : Preserves base (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ schedulerAtoms _ _ _ _ _
    encryptIteration cryptAhead (fun pid=>mixed _ (OwnerTransmit.txIteration pid)) decryptIteration receiveIteration a

theorem activationRun (a : Activation) : Preserves base (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves safe store _ schedulerAtoms _ activationIteration a

theorem dispatch (worker : Worker) : Preserves base (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves safe store _ schedulerAtoms _ activationRun worker

theorem schedule (stack : Option Worker) : Preserves base (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves safe store _ schedulerAtoms _ _ _ dispatch activationRun softirq stack


theorem nestedResched (worker : Worker) : Preserves base (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves safe store _ schedule worker

theorem sendOne : Preserves base (RxHistory.audit runOneSendWorkerAudit) := audit _ OwnerDeferred.sendOne
theorem clearOne : Preserves base (RxHistory.audit runOneClearWorkerAudit) := audit _ OwnerDeferred.clearOne
private theorem drained (what : String) (queues : List Bool) : Preserves base (RxHistory.mixed (requireDrainedPrefix what queues)) :=
  mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.drained) what queues)

theorem cryptWorkers : Preserves base RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves safe store _ (schedule none)

macro "release_deferred_steps" : tactic => `(tactic| first
  | (current_env_at RxHistory.schedule; exact schedule _)
  | (current_env_at RxHistory.runCryptWorkers; exact cryptWorkers)
  | (owner_env_outer RxHistory.audit; first | exact sendOne | exact clearOne)
  | (current_env_at runOneClearWorkerAudit; exact clearOne)
  | (current_env_at requireDrainedPrefix; exact drained _ _)
  | (current_env_at getWG; exact raw _ (fun initial=>productGetWG_spec (fun s=>s=initial)))
  | (current_env_at modifyWG; exact raw _ (fun initial=>productModifyWG_spec (fun s=>s=initial) _ (fun _=>rfl)))
  | (current_env_at Env.requireNoCryptWork; exact raw _ requireNoCryptWork_sameKernel)
  | (current_env_at Env.deliverSent; exact raw _ deliverSent_sameKernel)
  | scheduler_raw_steps safe store
  | (current_env_at Pure.pure; exact PrefixPreserves.pure safe _)
  | (current_env_at ForIn.forIn; first
      | apply PrefixPreserves.range (State := World) _ _ _ safe
      | apply PrefixPreserves.forIn _ _ _ safe)
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; split)
  | current_env_match
  | support_intro)

theorem sendWorkers : Preserves base RxHistory.runSendWorkers := by
  change PrefixPreserves (Inv base) OwnerChecks.Safe _
  unfold RxHistory.runSendWorkers
  repeat' release_deferred_steps

theorem afterXmit : Preserves base RxHistory.afterXmit := by
  change PrefixPreserves (Inv base) OwnerChecks.Safe _
  unfold RxHistory.afterXmit
  repeat' first
    | (current_env_at RxHistory.runSendWorkers; exact sendWorkers)
    | release_deferred_steps

private theorem audit_ensures (action : AuditM α)
    (spec : PrefixEnsures P S (RxHistory.audit action) Q) :
    PrefixEnsures (fun h w=>P h w ∧ Certificates base h) S (RxHistory.audit action)
      (fun x h w=>Q x h w ∧ Certificates base h) :=
  quiet_ensures _ (Appends.focus _ _ _)
    (fun w h=>focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent PollFatePromotion.removed (fun _=>rfl) action w h) spec

private theorem saved_spec : PrefixEnsures (Inv base) OwnerChecks.Safe (RxHistory.audit getDevSavedAudit)
    (fun d h w=>Inv base h w ∧ SavedPeers d.peers.toList (identityView w.wg)) := by
  apply PrefixEnsures.consequence
    (audit_ensures _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.saved_spec))
  · exact fun _ _ hi=>hi
  · exact fun _ _ _ hi=>⟨⟨hi.1.1,hi.2⟩,hi.1.2⟩

private theorem saved : Preserves base (RxHistory.audit getDevSavedAudit) :=
  audit _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.saved)

private theorem wheel_spec (d : Device) (j : UInt64) : PrefixEnsures
    (fun h w=>Inv base h w ∧ SavedPeers d.peers.toList (identityView w.wg))
    OwnerChecks.Safe (RxHistory.audit (wheelNextDueAudit d j)) (fun _=>Inv base) := by
  apply PrefixEnsures.consequence
    (audit_ensures _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.wheel_spec) d j))
  · exact fun _ _ hi=>⟨⟨hi.1.1,hi.2⟩,hi.1.2⟩
  · exact fun _ _ _ hi=>hi

private theorem stepComplete (b : UInt64) : Preserves base (RxHistory.audit (requireStepCompleteAudit b)) :=
  audit _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.stepComplete) b)
private theorem nothingDue (j : UInt64) : Preserves base (RxHistory.audit (requireNothingDueAudit j)) :=
  audit _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.nothingDue) j)
private theorem timerDispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer) (we : WheelEntry) (step : Option UInt64) :
    Preserves base (RxHistory.audit (timerDispatchAudit worker pid timer we step)) :=
  audit _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.timerDispatch) worker pid timer we step)
private theorem placeholderPass (j : UInt64) : Preserves base (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  audit _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.placeholderPass) j)

macro "release_timer_drop_saved" : tactic => `(tactic|
  (timer_audit_saved_pre; refine PrefixEnsures.consequence (P := (Inv _)) (Q := fun _ => (Inv _)) ?_
    (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)))

macro "release_timer_calls" : tactic => `(tactic|
  first
  | (rx_timer_head timerDispatchAudit; exact timerDispatch _ _ _ _ _)
  | (rx_timer_head requireStepCompleteAudit; exact stepComplete _)
  | (rx_timer_head requireNothingDueAudit; exact nothingDue _)
  | (rx_timer_head placeholderTimerPassAudit; exact placeholderPass _)
  | (rx_timer_head runOneSendWorkerAudit; exact sendOne)
  | (rx_timer_head runOneClearWorkerAudit; exact clearOne)
  | (rx_timer_head runCryptWorkers; exact cryptWorkers)
  | (rx_timer_head runSendWorkers; exact sendWorkers)
  | (rx_timer_head getWG; exact raw _ (by
      intro initial; exact productGetWG_spec (fun s => s = initial)))
  | (rx_timer_head modifyWG; exact raw _ (by
      intro initial; exact productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (rx_timer_head getEnv; exact raw _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (rx_timer_head Env.peekNextSite; exact raw _ peekNextSite_sameKernel)
  | (rx_timer_head Env.deliverSent; exact raw _ deliverSent_sameKernel)
  | (rx_timer_head unsupported; exact raw _ (fun initial=>productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi=>hi)))
  | (rx_timer_head throw; exact raw _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      cases hr))
  | (audit_contract_head liftPrefix; exact raw _ (by
      intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (rx_timer_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.1.safe) (fun _ _ hi => hi))
  | (rx_timer_head ForIn.forIn; apply PrefixEnsures.rangeInvariant (State := World)
      (I := fun _ h w => (Inv _) h w) (hs := fun _ _ _ hi => hi.1.safe)))

theorem timers (jHi : UInt64) : Preserves base (RxHistory.runTimers jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | contradiction
    | timer_audit_stopped
    | (rx_timer_bound getDevSavedAudit; first
        | (release_timer_drop_saved; apply PrefixEnsures.bind saved_spec)
        | apply PrefixEnsures.bind saved_spec)
    | (rx_timer_bound wheelNextDueAudit; apply PrefixEnsures.bind (wheel_spec _ _))
    | (release_timer_drop_saved; release_timer_calls)
    | release_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => (Inv _) h w))
    | (release_timer_drop_saved; maintenance_join_let)
    | maintenance_join_let
    | (release_timer_drop_saved; maintenance_join_use)
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split)
    | maintenance_intro

  all_goals
    apply PrefixEnsures.consequence (P := Inv base) (Q := fun _=>Inv base) _ (fun _ _ hi=>hi.1) (fun _ _ _ hi=>hi)
    exact raw _ (fun initial=>productAmbient_spec
      (unsupported "work a timer queued outlived the guest's wait" : AmbientM Bool)
      (fun s=>productStoreView s=initial) (fun _ _ hi=>hi))

theorem placeholder (jHi : UInt64) :
    Preserves base (RxHistory.runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (rx_timer_head RxHistory.runTimers; exact timers _)
    | (rx_timer_head getDevSavedAudit; exact saved)
    | release_timer_calls
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => (Inv _) h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

macro "release_deferred_timer_steps" : tactic => `(tactic| first
  | (environment_at "runOneSendWorkerAudit"; exact sendOne)
  | (environment_at "runOneClearWorkerAudit"; exact clearOne)
  | (environment_at "placeholderTimerPassAudit"; exact placeholderPass _)
  | (environment_at "timerDispatchAudit"; exact timerDispatch _ _ _ _ _)
  | (environment_at "requireStepCompleteAudit"; exact stepComplete _)
  | (environment_at "requireNothingDueAudit"; exact nothingDue _)
  | (environment_at "getDevSavedAudit"; exact saved)
  | (current_env_at peekSiteU64
     exact raw _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at hiddenJiffies
     exact raw _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at getEnv
     exact raw _ (by
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w x v hr
       cases hr
       rfl))
  | (current_env_at throw; exact raw _ (HistorySupport.source_throw _ _))
  | (current_env_at Env.peekNextSite; exact raw _ peekNextSite_sameKernel)
  | (current_env_at Env.timerWorker; exact raw _ (timerWorker_sameKernel _))
  | environment_reduce
  | environment_join
  | environment_join_use
  | release_deferred_steps)

theorem idle : Preserves base RxHistory.idleTimers := by
  change PrefixPreserves (Inv _) OwnerChecks.Safe _
  unfold RxHistory.idleTimers
  simp only [Functor.discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact timers _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact placeholder _)
    | release_deferred_timer_steps
  all_goals exact raw _ (fun initial=>productAmbient_spec
    (throw (Stop.hidden "no end-of-wait jiffies record (kind 310) in this operation") : AmbientM Unit)
    (fun s=>productStoreView s=initial) (fun _ _ hi=>hi))

theorem afterAdvance : Preserves base RxHistory.afterAdvance := by
  change PrefixPreserves (Inv _) OwnerChecks.Safe _
  unfold RxHistory.afterAdvance
  simp only [Functor.discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (current_env_at RxHistory.runTimers; exact timers _)
    | (current_env_at RxHistory.runTimersPlaceholder; exact placeholder _)
    | release_deferred_timer_steps
  all_goals exact raw _ (fun initial=>productAmbient_spec
    (throw (Stop.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance") : AmbientM Unit)
    (fun s=>productStoreView s=initial) (fun _ _ hi=>hi))


theorem deferred (call : EnvDeferredCall) : Preserves base (RxHistory.deferred call) := by
  cases call with
  | crypt=>exact cryptWorkers
  | sendAll=>exact sendWorkers
  | afterXmit=>exact afterXmit
  | timers j=>exact timers j
  | placeholder j=>exact placeholder j
  | idle=>exact idle
  | afterAdvance=>exact afterAdvance
  | drained what queues=>exact drained what queues
  | idleDevice=>exact mixed _ (OwnerDeferred.deferred .idleDevice)
  | sendOne=>exact sendOne
  | clearOne=>exact clearOne
  | noCrypt=>exact audit _ (OwnerDeferred.deferred .noCrypt)
  | timerWorker timer=>exact audit _ (OwnerDeferred.deferred (.timerWorker timer))
  | advance ticks=>exact audit _ (OwnerDeferred.deferred (.advance ticks))

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves base (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_preserves safe store _ _ _
    (fun msg src=>mixed _ (OwnerReceive.wgReceive_checked msg src)) cryptWorkers drained family port msg tos ll dest

theorem afterBatch : Preserves base RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves safe store _ _ _ _ _ cryptWorkers sendWorkers sendOne schedule drained

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Preserves base (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_preserves safe store _ _ _ _
    (fun msg src=>mixed _ (OwnerReceive.wgReceive_checked msg src)) inline afterBatch drained count port family messages

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Preserves base (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_preserves safe
    (fun h w v eq hi=>⟨OwnerControlCalls.store h w v eq hi.1,hi.2⟩) _ _ _ _
    (fun msg src=>mixed _ (OwnerReceive.wgReceive_checked msg src)) inline
    (fun family addr=>audit _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.multicast) family addr))
    (fun family addr packets mtu=>mixed _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.transmit) family addr packets mtu)) d cqes item

theorem batch (items : List Env.BatchItem) : Preserves base (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  exact TrafficSource.batch_preserves safe store _ _ batchItem afterBatch items

private theorem wgStore : ∀ h (w v : World),wgStoreView v.wg=wgStoreView w.wg→Inv base h w→Inv base h v :=
  fun h w v eq hi=>⟨OwnerControlCalls.store h w v eq hi.1,hi.2⟩

theorem observe : Preserves base RxHistory.observe :=
  PrefixPreserves.bind idle (fun _=>raw _ observeTail_sameKernel)

theorem socket (fd : Nat) (body : RxHistory.Obs Int) (hb : Preserves base body) :
    Preserves base (RxHistory.socketCallOn fd body) := by
  change PrefixPreserves (Inv base) OwnerChecks.Safe _
  unfold RxHistory.socketCallOn
  apply PrefixPreserves.bind (lift _ (OwnerControlCalls.lift_fs (fdget fd)))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure safe _
  · intro _
    exact hb.bind (fun ret=>(lift _ (OwnerControlCalls.lift_fs (fdput f))).bind
      (fun _=>PrefixPreserves.pure safe ret))

theorem syscallDispatch (call : Syscall) : Preserves base (RxHistory.syscallDispatch call) := by
  have owner := OwnerSyscalls.dispatch call
  cases call
  case wgInject family port msg tos ll dest=>exact socket _ _ (inject family port msg tos ll dest)
  case wgFlood count port family messages=>exact flood count port family messages
  case wgBatch items flags=>exact batch items
  case wgObserve=>
    unfold RxHistory.syscallDispatch
    apply PrefixPreserves.bind observe
    rintro ⟨ret,out⟩
    apply PrefixPreserves.bind (raw _ (fun initial=>productAmbient_spec _ _ (fun _ _ hi=>hi)))
    intro _
    exact socket _ _ (PrefixPreserves.pure safe _)
  all_goals exact audit _ owner

theorem syscall (call : Syscall) : Preserves base (RxHistory.syscall call) := by
  rw [Configuration.syscallRx_factor]
  exact SyscallSource.preserves safe wgStore call _ _ _ _ _ _ _ (syscallDispatch call)
    sendWorkers idle (audit _ OwnerRemaining.route) afterXmit afterAdvance (audit _ OwnerControlCalls.netnsCleanup)

/-- A certified position keeps the exact allocation-valid input used by its
actual normal poll, and hence a release in that same fresh promoted suffix. -/
theorem Certificate.release (hi : Certificate cut n skb stamp history) :
    ∃incoming w pid budget result v before after tail,
      cut=incoming++before.map RxHistory.promote ∧
      AllocationInv (RxHistory.prior incoming) w.wg ∧
      runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior incoming))=
        (.ok (result,v),RxJoint.seed (RxHistory.prior incoming)++(before++RxJoint.Event.removed n skb stamp::after)) ∧
      history=incoming++(before++RxJoint.Event.removed n skb stamp::after).map RxHistory.promote++tail ∧
      RxHistory.Released ((before++RxJoint.Event.removed n skb stamp::after).map RxHistory.promote) stamp := by
  obtain ⟨incoming,w,pid,budget,result,v,before,after,tail,position,allocation,run,hist⟩ := hi
  exact ⟨incoming,w,pid,budget,result,v,before,after,tail,position,allocation,run,hist,
    PollFatePromotion.normal_release pid budget w v incoming result before after n skb stamp allocation run⟩

theorem Certificate.fate (hi : Certificate cut n skb stamp history) :
    PollFatePromotion.Certificate cut n skb stamp history := by
  obtain ⟨incoming,w,pid,budget,result,v,before,after,tail,position,_,run,hist⟩ := hi
  exact ⟨incoming,w,pid,budget,result,v,before,after,tail,position,run,hist⟩

theorem Certificates.selected (hi : Certificates base history)
    (position : history=base++pre++RxHistory.Event.removed n skb stamp::post) :
    Certificate (base++pre) n skb stamp history := by
  obtain ⟨suffix,hist,checked⟩ := hi
  have split : suffix=pre++RxHistory.Event.removed n skb stamp::post :=
    List.append_cancel_left (by simpa only [List.append_assoc] using hist.symm.trans position)
  exact checked pre (.removed n skb stamp) post split

theorem normal (action : RxHistory.Obs α) (hp : Preserves incoming action)
    (owner : OwnerChecks.Inv incoming w)
    (run : runPrefix action w incoming=(.ok (value,v),history)) : Inv incoming history v := by
  obtain ⟨_,_,_,post⟩ := hp w incoming ⟨owner,initial incoming⟩
  simpa only [run] using post

end Leanux.Proofs.WG.Queues.RxCredits.PollReleaseCaller
