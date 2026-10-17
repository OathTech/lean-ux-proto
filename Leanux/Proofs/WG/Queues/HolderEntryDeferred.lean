import Leanux.Proofs.WG.Queues.HolderTrafficEntry
import Leanux.Proofs.WG.Queues.HolderAuxTimers

/-! Return-to-user waits retain the actual outer entry, including an absent
device. The absent branch has no physical-ring premise; its source guards
retain the original journal and store. Normal present branches use the actual
fresh removal suffix. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem readWG (w : World) :
    (getWG : Leanux.M WGWorld).run w = .ok (w.wg,w) := rfl

private theorem writeWG (f : WGWorld → WGWorld) (w : World) :
    (modifyWG f : Leanux.M Unit).run w = .ok ((),{w with wg:=f w.wg}) := rfl

theorem send_absent (absent : w.wg.dev=none) :
    runPrefix RxHistory.runSendWorkers w h=(.ok ((),w),h) := by
  simp only [RxHistory.runSendWorkers,runPrefix_bind,runPrefix_lift,readWG,
    absent,Option.isNone_none,↓reduceIte,runPrefix_pure]

theorem xmit_absent (absent : w.wg.dev=none) :
    runPrefix RxHistory.afterXmit w h=(.ok ((),w),h) := by
  simp only [RxHistory.afterXmit,runPrefix_bind,runPrefix_lift,readWG,absent,runPrefix_pure]

theorem timers_absent (j : UInt64) (absent : w.wg.dev=none) :
    runPrefix (RxHistory.runTimers j) w h=
      (.ok (false,{w with wg:={w.wg with queuedThisCall:=[]}}),h) := by
  simp only [RxHistory.runTimers,runPrefix_bind,runPrefix_lift,writeWG,readWG,
    absent,Option.isNone_none,↓reduceIte,runPrefix_pure]

theorem placeholder_absent (j : UInt64) (absent : w.wg.dev=none) :
    runPrefix (RxHistory.runTimersPlaceholder j) w h=
      (.ok ((),{w with wg:={w.wg with queuedThisCall:=[]}}),h) := by
  simp only [RxHistory.runTimersPlaceholder,runPrefix_bind,runPrefix_lift,writeWG,readWG,
    absent,Option.isNone_none,↓reduceIte,runPrefix_pure]

theorem nothingDue_absent (j : UInt64) (absent : w.wg.dev=none) :
    runPrefix (RxHistory.audit (requireNothingDueAudit j)) w h=(.ok ((),w),h) := by
  have localRun : runPrefix (requireNothingDueAudit j) w (h.filterMap RxHistory.auditEvent)=
      (.ok ((),w),h.filterMap RxHistory.auditEvent++[]) := by
    simp only [requireNothingDueAudit,runPrefix_bind,runPrefix_lift,readWG,
      absent,runPrefix_pure,List.append_nil]
  simpa only [RxHistory.audit,List.map_nil,List.append_nil] using
    focusPrefix_suffix RxHistory.Event.audit RxHistory.auditEvent _ w h _ [] localRun

private def Absent (initial : ProductStore43) (before : List RxHistory.Event)
    (h : List RxHistory.Event) (w : World) : Prop :=
  productStoreView w=initial ∧ w.wg.dev=none ∧ h=before

private theorem absent_transport (hi : Absent initial before h w)
    (same : productStoreView v=productStoreView w) : Absent initial before h v := by
  have dev : v.wg.dev=w.wg.dev := congrArg (fun s : ProductStore43=>s.2.2.2.dev) same
  exact ⟨same.trans hi.1,dev.trans hi.2.1,hi.2.2⟩

private theorem absent_timers (j : UInt64) :
    PrefixPreserves (Absent initial before) (fun _=>True) (RxHistory.runTimers j) := by
  intro w h hi
  rw [timers_absent j hi.2.1]
  exact ⟨[],by simp,True.intro,hi⟩

private theorem absent_placeholder (j : UInt64) :
    PrefixPreserves (Absent initial before) (fun _=>True) (RxHistory.runTimersPlaceholder j) := by
  intro w h hi
  rw [placeholder_absent j hi.2.1]
  exact ⟨[],by simp,True.intro,hi⟩

private theorem absent_nothingDue (j : UInt64) :
    PrefixPreserves (Absent initial before) (fun _=>True)
      (RxHistory.audit (requireNothingDueAudit j)) := by
  intro w h hi
  rw [nothingDue_absent j hi.2.1]
  exact ⟨[],by simp,True.intro,hi⟩

private theorem absent_idle :
    PrefixPreserves (Absent initial before) (fun _=>True) RxHistory.idleTimers := by
  have safe : ∀ h w,Absent initial before h w→True := fun _ _ _=>True.intro
  have saved : ∀ h w v,productStoreView v=productStoreView w→
      Absent initial before h w→Absent initial before h v := fun _ _ _ same hi=>absent_transport hi same
  unfold RxHistory.idleTimers
  repeat' first
    | (scheduler_preserve_at RxHistory.runTimers; exact absent_timers _)
    | (scheduler_preserve_at RxHistory.runTimersPlaceholder; exact absent_placeholder _)
    | (scheduler_preserve_at requireNothingDueAudit; exact absent_nothingDue _)
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves _ _ (RxHistory.runTimers _ >>= fun _=>pure ())
       exact PrefixPreserves.bind (absent_timers _) (fun _=>PrefixPreserves.pure safe ()))
    | deferred_raw_steps safe saved

private theorem absent_afterAdvance :
    PrefixPreserves (Absent initial before) (fun _=>True) RxHistory.afterAdvance := by
  have safe : ∀ h w,Absent initial before h w→True := fun _ _ _=>True.intro
  have saved : ∀ h w v,productStoreView v=productStoreView w→
      Absent initial before h w→Absent initial before h v := fun _ _ _ same hi=>absent_transport hi same
  unfold RxHistory.afterAdvance
  repeat' first
    | (scheduler_preserve_at RxHistory.runTimers; exact absent_timers _)
    | (scheduler_preserve_at RxHistory.runTimersPlaceholder; exact absent_placeholder _)
    | (scheduler_preserve_at requireNothingDueAudit; exact absent_nothingDue _)
    | (scheduler_preserve_at Functor.discard
       change PrefixPreserves _ _ (RxHistory.runTimers _ >>= fun _=>pure ())
       exact PrefixPreserves.bind (absent_timers _) (fun _=>PrefixPreserves.pure safe ()))
    | deferred_raw_steps safe saved

private theorem absent_send :
    PrefixPreserves (Absent initial before) (fun _=>True) RxHistory.runSendWorkers := by
  intro w h hi
  rw [send_absent hi.2.1]
  exact ⟨[],by simp,True.intro,hi⟩

private theorem absent_xmit :
    PrefixPreserves (Absent initial before) (fun _=>True) RxHistory.afterXmit := by
  intro w h hi
  rw [xmit_absent hi.2.1]
  exact ⟨[],by simp,True.intro,hi⟩

private theorem normal {action : RxHistory.Obs α}
    (account : ∀ initial loans before,PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe action)
    (structural : ∀ initial,PrefixPreserves (fun _ w=>BaseCoherence.view w.wg=initial) (fun _=>True) action)
    (absent : ∀ initial before,PrefixPreserves (Absent initial before) (fun _=>True) action)
    (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix action w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v := by
  cases dev:w.wg.dev with
  | some d => exact HolderTrafficEntry.auxiliary_normal account structural hi (by simp only [dev,Option.isSome_some]) run
  | none =>
    have post := (absent (productStoreView w) h w h ⟨rfl,dev,rfl⟩).choose_spec.2.2
    rw [run] at post
    have history : k=h := post.2.2
    have kept := HolderEntry.store hi post.1
    have empty : remaining cs (NapiCarrier.removedPackets [])=cs := List.filter_eq_self.mpr (fun _ _=>rfl)
    refine ⟨[],by simpa only [List.append_nil] using history,?_⟩
    simpa only [empty,history] using kept

/-- Includes the absent-device early return and every reached scheduler call. -/
theorem sendAll_normal (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix RxHistory.runSendWorkers w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  normal HolderAuxSend.runSendWorkers BaseCoherence.runSendWorkers_structure
    (fun _ _=>absent_send) hi run

/-- Both timer modes consume exactly their original records; an absent device
does not bypass the outer end-of-wait checks. -/
theorem idle_normal (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix RxHistory.idleTimers w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  normal HolderAuxTimers.idleTimers BaseCoherence.idleTimers_structure
    (fun _ _=>absent_idle) hi run

theorem afterXmit_normal (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix RxHistory.afterXmit w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  normal HolderAuxSend.afterXmit BaseCoherence.afterXmit_structure
    (fun _ _=>absent_xmit) hi run

theorem afterAdvance_normal (hi : HolderEntry.Inv cs loans h w)
    (run : runPrefix RxHistory.afterAdvance w h=(.ok (result,v),k)) :
    ∃ suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v :=
  normal HolderAuxTimers.afterAdvance BaseCoherence.afterAdvance_structure
    (fun _ _=>absent_afterAdvance) hi run

/-- Stopped executions retain the existing owner-safe reached journal. Only a
normal return supplies the next funded entry, at its exact fresh suffix. -/
private theorem checked {action : RxHistory.Obs α}
    (owner : OwnerChecks.Preserves action)
    (endpoint : ∀ {w v h k result},HolderEntry.Inv cs loans h w→
      runPrefix action w h=(.ok (result,v),k)→
      ∃ suffix,k=h++suffix ∧ HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :
    PrefixEnsures (fun h w=>h=before ∧ HolderEntry.Inv cs loans h w) OwnerChecks.Safe action
      (fun _ k v=>∃ suffix,k=before++suffix ∧
        HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) := by
  intro w h hi
  rcases hi with ⟨rfl,hi⟩
  obtain ⟨suffix,hist,safe,_⟩ := owner w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error reason => trivial
  | ok out => exact endpoint hi (Prod.ext run rfl)

theorem sendAll : PrefixEnsures
    (fun h w=>h=before ∧ HolderEntry.Inv cs loans h w) OwnerChecks.Safe RxHistory.runSendWorkers
    (fun _ k v=>∃ suffix,k=before++suffix ∧
      HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.runSendWorkers sendAll_normal

theorem idle : PrefixEnsures
    (fun h w=>h=before ∧ HolderEntry.Inv cs loans h w) OwnerChecks.Safe RxHistory.idleTimers
    (fun _ k v=>∃ suffix,k=before++suffix ∧
      HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.idleTimers idle_normal

theorem afterXmit : PrefixEnsures
    (fun h w=>h=before ∧ HolderEntry.Inv cs loans h w) OwnerChecks.Safe RxHistory.afterXmit
    (fun _ k v=>∃ suffix,k=before++suffix ∧
      HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.afterXmit afterXmit_normal

theorem afterAdvance : PrefixEnsures
    (fun h w=>h=before ∧ HolderEntry.Inv cs loans h w) OwnerChecks.Safe RxHistory.afterAdvance
    (fun _ k v=>∃ suffix,k=before++suffix ∧
      HolderEntry.Inv (remaining cs (NapiCarrier.removedPackets suffix)) loans k v) :=
  checked OwnerDeferred.afterAdvance afterAdvance_normal

end Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDeferred
