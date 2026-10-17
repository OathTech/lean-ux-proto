import Leanux.Proofs.WG.Queues.RxPollReceiptLink
import Leanux.Proofs.WG.Queues.RxScheduleHistory

/-! History-only linkage and receipt truth through the unchanged concrete
caller spine. Audit focus retains its actual incoming history and adds only
its actual audit suffix. The generic proof protocol below is instantiated
separately for linkage and receipt validity; neither changes allocation,
completion or operational observer definitions. -/
namespace Leanux.Proofs.WG.Queues.RxLink
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

/-- Check/consume-run and carried payload validity, separate from linkage and
from the Stack-return receipt protocol. -/
def HistoryReceiptsValid (h : List RxHistory.Event) : Prop :=
  RxDisposition.Valid (h.filterMap historyEvent)

abbrev Preserves (P : List RxHistory.Event → Prop) (a : RxHistory.Obs α) : Prop :=
  PrefixPreserves (fun h _ => P h) P a

/-- Proof interface for the actual poll and focused audit leaves. It does not
supply source coverage for an arbitrary operation hidden inside an audit. -/
class Protocol (P : List RxHistory.Event → Prop) : Prop where
  audit : ∀ {α : Type} (a : AuditM α), Preserves P (RxHistory.audit a)
  poll : ∀ pid budget, Preserves P (RxHistory.observePoll pid budget)
  origin : ∀ {α : Type} (a : PrefixM Origins.Event α),
    PrefixPreserves (fun h _ => Origins.Valid h) Origins.Valid a →
    Preserves P (Origins.HistoryAdapters.focus a)

theorem audit_from_suffix (P : List RxHistory.Event → Prop)
    (hp : ∀ h (s : List AuditEvent), P h → P (h ++ s.map RxHistory.Event.audit))
    (a : AuditM α) : Preserves P (RxHistory.audit a) := by
  intro w h hi
  let suffix := (runPrefix a w (h.filterMap RxHistory.auditEvent)).2.drop
    (h.filterMap RxHistory.auditEvent).length
  have hs := hp h suffix hi
  refine ⟨suffix.map RxHistory.Event.audit,rfl,hs,?_⟩
  cases (runPrefix (RxHistory.audit a) w h).1 <;> trivial

theorem linked_audit (a : AuditM α) : Preserves HistoryLinked (RxHistory.audit a) := by
  apply audit_from_suffix
  intro h s hi
  unfold HistoryLinked at hi ⊢
  rw [List.filterMap_append]
  apply linked_append_quiet hi
  intro e he pre
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [historyEvent,Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

theorem receipts_audit (a : AuditM α) : Preserves HistoryReceiptsValid (RxHistory.audit a) := by
  apply audit_from_suffix
  intro h s hi
  unfold HistoryReceiptsValid at hi ⊢
  rw [List.filterMap_append]
  apply (RxDisposition.valid_append _ _).mpr
  refine ⟨hi,?_⟩
  intro e he
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [historyEvent,Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

theorem observePoll_receipts (pid : PeerId) (budget : Nat) :
    Preserves HistoryReceiptsValid (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨s,hs,he,hv⟩ := RxDisposition.observePoll_receipt_suffix pid budget w h
  have valid : HistoryReceiptsValid (h ++ s.map RxHistory.promote) := by
    unfold HistoryReceiptsValid
    rw [List.filterMap_append,promote_history]
    exact (RxDisposition.valid_append _ _).mpr ⟨hi,hv⟩
  refine ⟨s.map RxHistory.promote,by rw [he],by simpa only [he] using valid,?_⟩
  rw [he]
  cases (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).1 <;> trivial

theorem linked_origin (a : PrefixM Origins.Event α) :
    Preserves HistoryLinked (Origins.HistoryAdapters.focus a) := by
  apply Origins.HistoryAdapters.focus_history
  intro h s hi
  unfold HistoryLinked at hi ⊢
  rw [List.filterMap_append]
  apply linked_append_quiet hi
  intro e he pre
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [Origins.HistoryAdapters.encode,historyEvent,Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

theorem receipts_origin (a : PrefixM Origins.Event α) :
    Preserves HistoryReceiptsValid (Origins.HistoryAdapters.focus a) := by
  apply Origins.HistoryAdapters.focus_history
  intro h s hi
  unfold HistoryReceiptsValid at hi ⊢
  rw [List.filterMap_append]
  apply (RxDisposition.valid_append _ _).mpr
  refine ⟨hi,?_⟩
  intro e he
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [Origins.HistoryAdapters.encode,historyEvent,Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

instance linkedProtocol : Protocol HistoryLinked :=
  ⟨linked_audit,observePoll_link,fun a _ => linked_origin a⟩
instance receiptsProtocol : Protocol HistoryReceiptsValid :=
  ⟨receipts_audit,observePoll_receipts,fun a _ => receipts_origin a⟩

variable {P : List RxHistory.Event → Prop} [Protocol P]

omit [Protocol P] in
theorem history_safe : ∀ h (_ : World), P h → P h := fun _ _ hi => hi

theorem audit_quiet (a : AuditM α) : Preserves P (RxHistory.audit a) := Protocol.audit a

theorem mixed_quiet (a : PrefixM LifetimeEvent α) : Preserves P (RxHistory.mixed a) := audit_quiet _

omit [Protocol P] in
theorem lift_quiet (a : Leanux.M α) : Preserves P (liftPrefix a) := by
  intro w h hi
  refine ⟨[],by simp,hi,?_⟩
  simp only [runPrefix_lift]
  cases a.run w <;> trivial

theorem prepare_quiet : Preserves P Origins.HistoryAdapters.prepare :=
  Protocol.origin _ Origins.HistoryAdapters.localPrepare_valid

theorem receiveStep_quiet : Preserves P Origins.HistoryAdapters.receiveStep :=
  Protocol.origin _ Origins.HistoryAdapters.localStep_valid

theorem receiveIteration_quiet : Preserves P Origins.HistoryAdapters.receiveIteration :=
  Origins.HistoryAdapters.receiveIteration_history P receiveStep_quiet

theorem napiSoftirq_preserves : Preserves P RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves history_safe (fun _ _ _ _ hi => hi)
    (audit_quiet _) Protocol.poll

theorem pollScheduledInline_preserves : Preserves P RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves history_safe (fun _ _ _ _ hi => hi)
    (audit_quiet _) Protocol.poll

theorem napiIrqExit_preserves : Preserves P RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves history_safe (fun _ _ _ _ hi => hi)
    (audit_quiet _) napiSoftirq_preserves

macro "link_steps" : tactic => `(tactic|
  repeat' first
    | with_reducible exact audit_quiet _
    | with_reducible exact mixed_quiet _
    | exact prepare_quiet
    | exact receiveIteration_quiet
    | with_reducible exact lift_quiet _
    | with_reducible exact PrefixPreserves.pure history_safe _
    | with_reducible apply PrefixPreserves.range _ _ _ history_safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ history_safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem encryptIteration_preserves : Preserves P RxHistory.encryptIteration :=
  PrefixPreserves.bind (mixed_quiet _) (fun _ =>
    PrefixPreserves.bind napiSoftirq_preserves (fun _ => mixed_quiet _))

theorem decryptStep_preserves : Preserves P RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  repeat' first
    | with_reducible exact napiSoftirq_preserves
    | with_reducible exact napiIrqExit_preserves
    | link_steps

theorem decryptIteration_preserves : Preserves P RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ history_safe decryptStep_preserves
  exact PrefixPreserves.bind (lift_quiet _) (fun _ => lift_quiet _)

theorem cryptAhead_preserves (pid : PeerId) : Preserves P (RxHistory.cryptAhead pid) := by
  unfold RxHistory.cryptAhead
  repeat' first
    | with_reducible exact encryptIteration_preserves
    | link_steps

theorem activationIteration_preserves (a : Activation) :
    Preserves P (RxHistory.activationIteration a) := by
  unfold RxHistory.activationIteration
  repeat' first
    | with_reducible exact encryptIteration_preserves
    | with_reducible exact decryptIteration_preserves
    | with_reducible exact cryptAhead_preserves _
    | link_steps

theorem activationRun_preserves (a : Activation) :
    Preserves P (RxHistory.activationRun a) := by
  unfold RxHistory.activationRun
  repeat' first
    | with_reducible exact activationIteration_preserves _
    | link_steps

theorem dispatch_preserves (worker : Worker) : Preserves P (RxHistory.dispatch worker) := by
  unfold RxHistory.dispatch
  repeat' first
    | with_reducible exact activationRun_preserves _
    | link_steps

/-- The actual consistency-filter audit is protocol-quiet. Its saved trial
Worlds and histories are untouched; no trial receipt enters this journal. -/
theorem schedule_preserves (stack : Option Worker) : Preserves P (RxHistory.schedule stack) := by
  unfold RxHistory.schedule
  simp only [List.find?_cons, List.find?_nil]
  repeat' first
    | with_reducible exact dispatch_preserves _
    | with_reducible exact activationRun_preserves _
    | with_reducible exact napiSoftirq_preserves
    | link_steps

theorem nestedResched_preserves (self : Worker) : Preserves P (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_quiet _)
  intro b
  split
  · exact schedule_preserves _
  · exact PrefixPreserves.pure history_safe _

end Leanux.Proofs.WG.Queues.RxLink
