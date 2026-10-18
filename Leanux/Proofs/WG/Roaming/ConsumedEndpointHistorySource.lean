import Leanux.Proofs.WG.Roaming.ConsumedEndpointSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ConsumedEndpoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes RxJoint
variable {α β : Type}

def HistoryChecks (h : List RxHistory.Event) : Prop :=
  Checks (h.filterMap RxLink.historyEvent)

theorem observePoll_checks (pid : PeerId) (budget : Nat) :
    RxLink.Preserves HistoryChecks (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨suffix,append⟩ := RxJoint.poll_appends pid budget w (seed (RxHistory.prior h))
  have whole := (poll_checks pid budget w (seed (RxHistory.prior h))
    (by intro e member; obtain ⟨x,_,rfl⟩ := List.mem_map.mp member; trivial)).choose_spec.2.1
  rw [append] at whole
  have suffixChecked : Checks suffix :=
    fun e member => whole e (List.mem_append_right _ member)
  have run := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl append)
  have checked : HistoryChecks (h ++ suffix.map RxHistory.promote) := by
    unfold HistoryChecks
    rw [List.filterMap_append,RxLink.promote_history]
    exact checks_append hi suffixChecked
  refine ⟨suffix.map RxHistory.promote,by rw [run],by simpa only [run] using checked,?_⟩
  rw [run]
  cases (runPrefix (RxJoint.poll pid budget) w (seed (RxHistory.prior h))).1 <;> trivial

theorem audit_checks (a : AuditM α) : RxLink.Preserves HistoryChecks (RxHistory.audit a) := by
  apply RxLink.audit_from_suffix
  intro h s hi
  unfold HistoryChecks at hi ⊢
  rw [List.filterMap_append]
  apply checks_append hi
  intro e he
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [RxLink.historyEvent,Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

theorem origin_checks (a : PrefixM Origins.Event α) :
    RxLink.Preserves HistoryChecks (Origins.HistoryAdapters.focus a) := by
  apply Origins.HistoryAdapters.focus_history
  intro h s hi
  unfold HistoryChecks at hi ⊢
  rw [List.filterMap_append]
  apply checks_append hi
  intro e he
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp he
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hx
  cases x <;> simp only [Origins.HistoryAdapters.encode,RxLink.historyEvent,
    Option.some.injEq,reduceCtorEq] at he
  subst e
  trivial

instance endpointProtocol : RxLink.Protocol HistoryChecks :=
  ⟨audit_checks,observePoll_checks,fun a _ => origin_checks a⟩

theorem initialized_checks (trace : Runner.Trace) (placeholders : Bool) :
    HistoryChecks (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RxLink.executeTraceHistory_protocol trace placeholders (by intro e member; cases member)

theorem initialized_endpoint (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (n id : Nat) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed n id stamp r :: post) : Facts r := by
  apply initialized_checks trace placeholders (.consumed n id stamp r)
  apply List.mem_filterMap.mpr
  refine ⟨.consumed n id stamp r,?_,rfl⟩
  rw [position]
  simp


end Leanux.Proofs.WG.Roaming.ConsumedEndpoint
