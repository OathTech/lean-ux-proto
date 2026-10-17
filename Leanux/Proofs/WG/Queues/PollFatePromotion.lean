import Leanux.Proofs.WG.Queues.RxLinkPositions
import Leanux.Proofs.WG.Queues.RxLinkEnvironment
import Leanux.Proofs.WG.Queues.NapiSource
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.DeferredPreservation
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! Exact removal positions retain their actual normal poll invocation and
its incoming outer history. Local occurrence numbers are never treated as
global identities. A Stop receives no completed-poll or state assertion. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.PollFatePromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- A selected global removal position belongs to this particular completed
local poll. Its entire promoted suffix is already in the returned journal. -/
def Certificate (cut : List RxHistory.Event) (n skb : Nat) (stamp : PacketStamp)
    (history : List RxHistory.Event) : Prop :=
  ∃ incoming w pid budget result v before after tail,
    cut=incoming++before.map RxHistory.promote ∧
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
def Inv (base history : List RxHistory.Event) : Prop :=
  ∃suffix,history=base++suffix ∧ ∀pre event post,suffix=pre++event::post→
    EventCertificate (base++pre) event history

abbrev Preserves (base : List RxHistory.Event) (action : RxHistory.Obs α) :=
  PrefixPreserves (fun h (_ : World)=>Inv base h) (fun _=>True) action

theorem initial (base : List RxHistory.Event) : Inv base base := by
  refine ⟨[],by simp,?_⟩
  intro pre event post impossible
  cases pre <;> cases impossible

theorem Certificate.append (hi : Certificate cut n skb stamp h) (suffix : List RxHistory.Event) :
    Certificate cut n skb stamp (h++suffix) := by
  obtain ⟨incoming,w,pid,budget,result,v,before,after,tail,position,run,hist⟩ := hi
  exact ⟨incoming,w,pid,budget,result,v,before,after,tail++suffix,position,run,
    by rw [hist,List.append_assoc]⟩

theorem EventCertificate.append (hi : EventCertificate cut event h) (suffix : List RxHistory.Event) :
    EventCertificate cut event (h++suffix) := by
  cases event <;> first | trivial | exact Certificate.append hi suffix

theorem append (hi : Inv base h) (suffix : List RxHistory.Event)
    (fresh : ∀pre event post,suffix=pre++event::post→EventCertificate (h++pre) event (h++suffix)) :
    Inv base (h++suffix) := by
  obtain ⟨old,hist,checked⟩ := hi
  refine ⟨old++suffix,by rw [hist,List.append_assoc],?_⟩
  apply (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (fun pre event=>EventCertificate (base++pre) event (h++suffix)) old suffix
  · intro pre event post position
    exact (checked pre event post position).append suffix
  · intro pre event post position
    simpa only [←List.append_assoc,←hist] using fresh pre event post position

def removed : RxHistory.Event→Option RxJoint.EntryKey
  | .removed n skb stamp=>some (n,skb,stamp)
  | _=>none

theorem quiet (action : RxHistory.Obs α) (appends : Appends action)
    (frame : HistoryFrame removed action) : Preserves base action := by
  intro w h hi
  obtain ⟨suffix,hist⟩ := appends w h
  have emptySuffix : suffix.filterMap removed=[] := by
    have same := frame w h
    rw [hist,List.filterMap_append] at same
    exact List.append_cancel_left (by simpa only [List.append_nil] using same)
  have kept : Inv base (h++suffix) := append hi suffix (by
    intro pre event post position
    have noEvent : removed event=none := by
      have empty := emptySuffix
      rw [position,List.filterMap_append,List.filterMap_cons] at empty
      cases he : removed event <;> simp_all
    cases event <;> first | trivial | cases noEvent)
  refine ⟨suffix,hist,True.intro,?_⟩
  cases run:(runPrefix action w h).1 with
  | error reason=>trivial
  | ok out=>simpa only [hist] using kept

theorem lift (action : Leanux.M α) : Preserves base (liftPrefix action) :=
  quiet _ (Appends.lift _) (HistoryFrame.lift _ _)

theorem audit (action : AuditM α) : Preserves base (RxHistory.audit action) :=
  quiet _ (Appends.focus _ _ _) (fun w h=>
    focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent removed (fun _=>rfl) action w h)

theorem mixed (action : PrefixM LifetimeEvent α) : Preserves base (RxHistory.mixed action) := audit _

theorem origin (action : PrefixM Origins.Event α) : Preserves base (Origins.HistoryAdapters.focus action) :=
  quiet _ (Appends.focus _ _ _)
    (Origins.HistoryAdapters.focus_other removed (by intro e;cases e <;> rfl) action)

private theorem filterMap_some {A B : Type} (f : A→B) (xs : List A) :
    xs.filterMap (fun x=>some (f x))=xs.map f := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.filterMap_cons,List.map_cons,ih]

/-- The selected local ordinal and both outer cuts are retained at promotion. -/
theorem poll (pid : PeerId) (budget : Nat) : Preserves base (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨suffix,localHist⟩ := RxJoint.poll_appends pid budget w (RxJoint.seed (RxHistory.prior h))
  have observed := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl localHist)
  refine ⟨suffix.map RxHistory.promote,by rw [observed],True.intro,?_⟩
  rw [observed]
  cases actual:(runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).1 with
  | error reason=>trivial
  | ok out=>
    apply append hi
    intro pre event post position
    cases event <;> try trivial
    case removed n skb stamp=>
      obtain ⟨before,e,after,hist,hbefore,he,hafter⟩ :=
        RxLink.filterMap_position (fun e=>some (RxHistory.promote e)) suffix pre (.removed n skb stamp) post
          (by simpa only [filterMap_some] using position)
      have value : e=RxJoint.Event.removed n skb stamp := by
        cases e <;> cases he <;> rfl
      subst e
      refine ⟨h,w,pid,budget,out.1,out.2,before,after,[],?_,?_,?_⟩
      · simpa only [filterMap_some] using congrArg (h++·) hbefore.symm
      · exact Prod.ext actual (by rw [localHist,hist])
      · simp only [hist,List.append_nil]

private theorem safe : ∀ h w, (fun h (_ : World)=>Inv base h) h w → True := fun _ _ _=>True.intro
private theorem store : ∀ h (w v : World), productStoreView v=productStoreView w → Inv base h → Inv base h :=
  fun _ _ _ _ hi=>hi

theorem softirq : Preserves base RxHistory.napiSoftirq := by
  rw [NapiSource.softirq_factor]
  exact RxNapi.softirq_preserves safe store (audit _) poll

theorem inline : Preserves base RxHistory.pollScheduledInline := by
  rw [NapiSource.inline_factor]
  exact RxNapi.inline_preserves safe store (audit _) poll

theorem irqExit : Preserves base RxHistory.napiIrqExit := by
  rw [NapiSource.irqExit_factor]
  exact RxNapi.irqExit_preserves safe store (audit _) softirq

theorem decrypt : Preserves base RxHistory.decryptStep := by
  rw [NapiSource.decrypt_factor]
  exact NapiSource.decrypt_preserves safe (origin _) (fun _=>mixed _) softirq irqExit

theorem decryptIteration : Preserves base RxHistory.decryptIteration := by
  rw [NapiSource.decryptIteration_factor]
  apply workerIterPrefix_preserves _ _ safe decrypt
  exact PrefixPreserves.bind (lift _) (fun _=>lift _)

theorem receiveIteration : Preserves base Origins.HistoryAdapters.receiveIteration :=
  workerIterPrefix_preserves _ _ safe (origin _) (lift _)

theorem encryptIteration : Preserves base RxHistory.encryptIteration :=
  PrefixPreserves.bind (mixed _) (fun _=>PrefixPreserves.bind softirq (fun _=>mixed _))

private theorem schedulerAtoms : RxHistory.SchedulerSource.AtomContracts
    (fun h (_ : World)=>Inv base h) (fun _=>True) (fun {_} a=>a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals intros; first | exact mixed _ | exact audit _

theorem cryptAhead (pid : PeerId) : Preserves base (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves safe _ schedulerAtoms _ encryptIteration pid

theorem activationIteration (a : Activation) : Preserves base (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ schedulerAtoms _ _ _ _ _
    encryptIteration cryptAhead (fun _=>mixed _) decryptIteration receiveIteration a

theorem activationRun (a : Activation) : Preserves base (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves safe store _ schedulerAtoms _ activationIteration a

theorem dispatch (worker : Worker) : Preserves base (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves safe store _ schedulerAtoms _ activationRun worker

theorem schedule (stack : Option Worker) : Preserves base (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves safe store _ schedulerAtoms _ _ _ dispatch activationRun softirq stack

private theorem deferredAtoms : RxHistory.DeferredSource.AtomContracts
    (fun h (_ : World)=>Inv base h) (fun _=>True) (fun {_} a=>a) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals intros; first | exact audit _ | exact mixed _

theorem cryptWorkers : Preserves base RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves safe store _ (schedule none)

theorem sendWorkers : Preserves base RxHistory.runSendWorkers := by
  rw [RxHistory.DeferredSource.send_factor]
  exact RxHistory.DeferredSource.send_preserves safe store _ deferredAtoms _ (schedule none)

theorem afterXmit : Preserves base RxHistory.afterXmit := by
  rw [RxHistory.DeferredSource.afterXmit_factor]
  exact RxHistory.DeferredSource.afterXmit_preserves safe store _ deferredAtoms _ cryptWorkers _ sendWorkers

theorem timers (j : UInt64) : Preserves base (RxHistory.runTimers j) := by
  rw [RxHistory.DeferredSource.timers_factor]
  exact RxHistory.DeferredSource.timers_preserves safe store _ deferredAtoms _ cryptWorkers j

theorem placeholder (j : UInt64) : Preserves base (RxHistory.runTimersPlaceholder j) := by
  rw [RxHistory.DeferredSource.placeholder_factor]
  exact RxHistory.DeferredSource.placeholder_preserves safe store _ deferredAtoms _ cryptWorkers _ sendWorkers j

theorem idle : Preserves base RxHistory.idleTimers := by
  rw [RxHistory.DeferredSource.idle_factor]
  exact RxHistory.DeferredSource.idle_preserves safe store _ deferredAtoms _ timers _ placeholder

theorem afterAdvance : Preserves base RxHistory.afterAdvance := by
  rw [RxHistory.DeferredSource.afterAdvance_factor]
  exact RxHistory.DeferredSource.afterAdvance_preserves safe store _ deferredAtoms _ timers _ placeholder

theorem deferred (call : EnvDeferredCall) : Preserves base (RxHistory.deferred call) := by
  rw [RxHistory.DeferredSource.deferred_factor]
  exact RxHistory.DeferredSource.deferred_preserves _ deferredAtoms _ _ _ _ _ _ _
    cryptWorkers sendWorkers afterXmit timers placeholder idle afterAdvance call

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves base (RxHistory.inject family port msg tos ll dest) := by
  rw [TrafficSource.inject_factor]
  exact TrafficSource.inject_preserves safe store _ _ _ (fun _ _=>mixed _) cryptWorkers
    (fun _ _=>mixed _) family port msg tos ll dest

theorem afterBatch : Preserves base RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves safe store _ _ _ _ _ cryptWorkers sendWorkers
    (audit _) schedule (fun _ _=>mixed _)

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Preserves base (RxHistory.flood count port family messages) := by
  rw [TrafficSource.flood_factor]
  exact TrafficSource.flood_preserves safe store _ _ _ _ (fun _ _=>mixed _) inline afterBatch
    (fun _ _=>mixed _) count port family messages

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Preserves base (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_preserves safe (fun _ _ _ _ hi=>hi) _ _ _ _
    (fun _ _=>mixed _) inline (fun _ _=>audit _) (fun _ _ _ _=>mixed _) d cqes item

theorem batch (items : List Env.BatchItem) : Preserves base (RxHistory.batch items) := by
  rw [TrafficSource.batch_factor]
  exact TrafficSource.batch_preserves safe store _ _ batchItem afterBatch items

/-- A normal local removal has one actual checked nondelivery decision or an
actual completed stack callback. The key includes ordinal, slot and stamp. -/
def Fate (key : RxJoint.EntryKey) (h : List RxJoint.Event) : Prop :=
  (∃ e ∈ h, RxDisposition.nondeliveryKey e=some key ∧ RxDisposition.EventValid e) ∨
  (∃ e r, RxJoint.Event.completed e r∈h ∧ e.key=key ∧
    RxDisposition.ConsumePayloadValid e ∧ r.Valid (Env.Stack.receive e.tag.bytes))

private theorem nondelivery_settled {e : RxJoint.Event} {key : RxJoint.EntryKey}
    (he : RxDisposition.nondeliveryKey e=some key) : RxDisposition.settledKey e=some key := by
  cases e <;> first | exact he | cases he

private theorem completed_member {h : List RxJoint.Event} {e : RxJoint.Entry}
    (he : e∈RxDisposition.completedEntries h) : ∃r,RxJoint.Event.completed e r∈h := by
  obtain ⟨step,hs,eq⟩ := List.mem_filterMap.mp he
  obtain ⟨event,hm,hj⟩ := List.mem_filterMap.mp hs
  cases event <;> simp only [RxCompletion.jointEvent,Option.some.injEq,reduceCtorEq] at hj
  all_goals subst step
  all_goals simp only [RxCompletion.completed,Option.some.injEq,reduceCtorEq] at eq
  subst e
  exact ⟨_,hm⟩

theorem normal_fate (pid : PeerId) (budget : Nat) (w v : World) (prior : List LifetimeEvent)
    (result : Nat) (hr : (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed prior)).1=.ok (result,v))
    (key : RxJoint.EntryKey)
    (selected : key∈RxJoint.removalKeys (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed prior)).2) :
    Fate key (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed prior)).2 := by
  let h := (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed prior)).2
  obtain ⟨account,_,_,partition,_⟩ := RxDisposition.poll_normal_partition pid budget w v prior result hr
  obtain ⟨_,_,_,_,unique⟩ := RxDisposition.poll_partition pid budget w prior
  have member : key.1∈(h.filterMap RxDisposition.nondeliveryKey).map Prod.fst ++
      (RxDisposition.completedEntries h).map (fun e=>e.tag.occurrence) :=
    partition.mem_iff.mp (List.mem_map.mpr ⟨key,selected,rfl⟩)
  rcases List.mem_append.mp member with dropped | completed
  · obtain ⟨other,hm,eq⟩ := List.mem_map.mp dropped
    obtain ⟨event,he,hkey⟩ := List.mem_filterMap.mp hm
    have old : other∈RxJoint.removalKeys h := by
      change RxJoint.removalKeys h=RxDisposition.settledKeys h++Option.toList (none : Option RxJoint.EntryKey) at account
      rw [account]
      exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨event,he,nondelivery_settled hkey⟩)
    have same : other=key := RxJoint.key_eq_of_nodup_map unique old selected eq
    subst other
    exact Or.inl ⟨event,he,hkey,RxDisposition.poll_seed_valid pid budget w prior event he⟩
  · obtain ⟨entry,hm,eq⟩ := List.mem_map.mp completed
    obtain ⟨_,_,_,normal⟩ := RxCompletion.poll_preserves pid budget w (RxJoint.seed prior)
      (by simp only [RxCompletion.Closed,RxCompletion.seed_empty];exact RxCompletion.ClosedTrace.nil)
    have closed : RxCompletion.ClosedTrace (h.filterMap RxCompletion.jointEvent) := by
      simpa only [hr,RxCompletion.Closed] using normal
    have entries : RxJoint.entries h=RxDisposition.completedEntries h := by
      simpa only [RxCompletion.joint_entries,RxDisposition.completedEntries] using closed.matches
    have old : entry.key∈RxJoint.removalKeys h :=
      RxJoint.poll_entry_support pid budget w prior entry (entries.symm ▸ hm)
    have same : entry.key=key := RxJoint.key_eq_of_nodup_map unique old selected eq
    obtain ⟨receipt,mem⟩ := completed_member hm
    exact Or.inr ⟨entry,receipt,mem,same,(RxDisposition.poll_receipts pid budget w prior).2.1 entry receipt mem⟩

/-- This is a fresh source release, not just absence in the final store. Its
allocation premise belongs to the actual captured input of this invocation. -/
theorem normal_release (pid : PeerId) (budget : Nat) (w v : World)
    (incoming : List RxHistory.Event) (result : Nat) (before after : List RxJoint.Event)
    (n skb : Nat) (stamp : PacketStamp)
    (hi : AllocationInv (RxHistory.prior incoming) w.wg)
    (run : runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior incoming))=
      (.ok (result,v),RxJoint.seed (RxHistory.prior incoming)++(before++RxJoint.Event.removed n skb stamp::after))) :
    RxHistory.Released ((before++RxJoint.Event.removed n skb stamp::after).map RxHistory.promote) stamp := by
  apply (RxHistory.released_promote _ _).mpr
  have rel := RxJoint.poll_suffix_removal_release pid budget w (RxHistory.prior incoming) hi
    (before++RxJoint.Event.removed n skb stamp::after) (congrArg Prod.snd run)
  simp only [run] at rel
  apply rel (n,skb,stamp)
  apply List.mem_filterMap.mpr
  exact ⟨.removed n skb stamp,by simp,rfl⟩

/-- Each fresh exact removal position selects its own invocation certificate. -/
theorem Inv.selected (hi : Inv base history)
    (position : history=base++pre++RxHistory.Event.removed n skb stamp::post) :
    Certificate (base++pre) n skb stamp history := by
  obtain ⟨suffix,hist,checked⟩ := hi
  have split : suffix=pre++RxHistory.Event.removed n skb stamp::post :=
    List.append_cancel_left (by simpa only [List.append_assoc] using hist.symm.trans position)
  exact checked pre (.removed n skb stamp) post split

/-- Actual normal output constructs the exact fresh-position invariant. -/
theorem normal (action : RxHistory.Obs α) (hp : Preserves incoming action)
    (run : runPrefix action w incoming=(.ok (value,v),history)) : Inv incoming history := by
  obtain ⟨_,_,_,post⟩ := hp w incoming (initial incoming)
  simpa only [run] using post

private theorem Fate.drop_seed (hf : Fate key (RxJoint.seed prior++suffix)) : Fate key suffix := by
  rcases hf with ⟨event,mem,hkey,valid⟩ | ⟨entry,receipt,mem,hkey,valid⟩
  · refine Or.inl ⟨event,?_,hkey,valid⟩
    rcases List.mem_append.mp mem with old | new
    · obtain ⟨e,_,rfl⟩ := List.mem_map.mp old
      cases hkey
    · exact new
  · refine Or.inr ⟨entry,receipt,?_,hkey,valid⟩
    rcases List.mem_append.mp mem with old | new
    · obtain ⟨e,_,eq⟩ := List.mem_map.mp old
      cases eq
    · exact new

/-- Classification stays attached to the same invocation and strict global
position. Equal local ordinals from different polls are not identified. -/
theorem Certificate.classified (hi : Certificate cut n skb stamp history) :
    ∃ incoming w pid budget result v before after tail,
      cut=incoming++before.map RxHistory.promote ∧
      runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior incoming))=
        (.ok (result,v),RxJoint.seed (RxHistory.prior incoming)++(before++RxJoint.Event.removed n skb stamp::after)) ∧
      history=incoming++(before++RxJoint.Event.removed n skb stamp::after).map RxHistory.promote++tail ∧
      Fate (n,skb,stamp) (before++RxJoint.Event.removed n skb stamp::after) := by
  obtain ⟨incoming,w,pid,budget,result,v,before,after,tail,position,run,hist⟩ := hi
  refine ⟨incoming,w,pid,budget,result,v,before,after,tail,position,run,hist,?_⟩
  apply Fate.drop_seed (prior:=RxHistory.prior incoming)
  have fate := normal_fate pid budget w v (RxHistory.prior incoming) result (congrArg Prod.fst run)
    (n,skb,stamp) (by
      rw [run]
      exact List.mem_filterMap.mpr ⟨.removed n skb stamp,by simp,rfl⟩)
  simpa only [run] using fate

/-- A nondelivery receipt names the actual state rejection, counter rejection,
or normal None consume. An endpoint None is impossible in the source. -/
theorem named_nondelivery {key : RxJoint.EntryKey} {event : RxJoint.Event}
    (selected : RxDisposition.nondeliveryKey event=some key) (valid : RxDisposition.EventValid event) :
    (∃ pkt r,event=RxJoint.Event.checkedState key.1 key.2.1 key.2.2 pkt r ∧
      r.value=true ∧ r.Valid (branch .rxPollNotCrypted (pkt.state != .crypted))) ∨
    (∃ pkt r,event=RxJoint.Event.checkedCounter key.1 key.2.1 key.2.2 pkt r ∧
      r.value=false ∧ r.Valid (liftWG (counterValidate pkt.keypair pkt.nonce))) ∨
    (∃ r,event=RxJoint.Event.consumed key.1 key.2.1 key.2.2 r ∧ r.run.value=none ∧ r.Valid) := by
  cases event <;> simp only [RxDisposition.nondeliveryKey,RxDisposition.settledKey,reduceCtorEq] at selected
  case checkedState n skb stamp pkt r =>
    split at selected
    next yes =>
      cases selected
      exact Or.inl ⟨pkt,r,rfl,yes,valid⟩
    next no => cases selected
  case checkedCounter n skb stamp pkt r =>
    split at selected
    next yes => cases selected
    next no =>
      cases selected
      exact Or.inr (Or.inl ⟨pkt,r,rfl,Bool.eq_false_iff.mpr no,valid⟩)
  case checkedEndpoint n skb stamp pkt r =>
    split at selected
    next yes => exact False.elim (RxDisposition.endpoint_none_impossible pkt r valid (Option.isNone_iff_eq_none.mp yes))
    next no => cases selected
  case consumed n skb stamp r =>
    split at selected
    next yes =>
      cases selected
      exact Or.inr (Or.inr ⟨r,rfl,Option.isNone_iff_eq_none.mp yes,valid⟩)
    next no => cases selected

end Leanux.Proofs.WG.Queues.RxCredits.PollFatePromotion
