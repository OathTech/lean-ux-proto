import Leanux.Proofs.WG.Queues.JointRunner
import Leanux.Proofs.WG.Queues.RxPollReceiptLink
import Leanux.Proofs.WG.Origins.CurrentChecks

/-! Exact occurrence elimination for the existing receive linkage journal.
Equal event values do not identify positions. Projection reconstructs the
selected prefix and suffix, retaining every discarded other-variant event. -/
namespace Leanux.Proofs.WG.Queues.RxLink
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

/-- Each position after the arbitrary incoming base has its own link. -/
theorem Linked.positions (hi : Linked base h) :
    ∃ suffix, h = base ++ suffix ∧
      ∀ pre e post, suffix = pre ++ e :: post → EventLink base (base ++ pre) e := by
  induction hi with
  | start =>
    refine ⟨[],by simp,?_⟩
    intro pre e post impossible
    cases pre <;> cases impossible
  | @snoc h e old he ih =>
    obtain ⟨suffix,hs,checked⟩ := ih
    refine ⟨suffix ++ [e],by simp only [hs,List.append_assoc],?_⟩
    apply (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
      (fun pre e => EventLink base (base ++ pre) e) suffix [e] checked
    intro pre event post position
    cases pre with
    | nil =>
      simp only [List.nil_append,List.cons.injEq] at position
      obtain ⟨rfl,rfl⟩ := position
      simpa only [List.append_nil,← hs] using he
    | cons first rest =>
      have length := congrArg List.length position
      simp only [List.length_cons,List.length_nil,List.length_append] at length
      omega

/-- Eliminate the specified occurrence, rather than a membership witness. -/
theorem Linked.at (hi : Linked base h)
    (position : h = base ++ pre ++ e :: post) : EventLink base (base ++ pre) e := by
  obtain ⟨suffix,hs,checked⟩ := hi.positions
  have same : suffix = pre ++ e :: post :=
    List.append_cancel_left (hs.symm.trans (by simpa only [List.append_assoc] using position))
  exact checked pre e post same

/-- Lift one specified filtered occurrence while preserving both exact cuts. -/
theorem filterMap_position {A B : Type} (f : A → Option B) (h : List A)
    (pre : List B) (e : B) (post : List B)
    (position : h.filterMap f = pre ++ e :: post) :
    ∃ left x right, h = left ++ x :: right ∧ left.filterMap f = pre ∧
      f x = some e ∧ right.filterMap f = post := by
  induction h generalizing pre with
  | nil => cases pre <;> cases position
  | cons x xs ih =>
    cases hx : f x with
    | none =>
      have tail : xs.filterMap f = pre ++ e :: post := by
        simpa only [List.filterMap_cons,hx] using position
      obtain ⟨left,y,right,hs,hl,hy,hr⟩ := ih pre tail
      exact ⟨x :: left,y,right,by simp only [hs,List.cons_append],
        by simp only [List.filterMap_cons,hx,hl],hy,hr⟩
    | some y =>
      cases pre with
      | nil =>
        have same : y = e ∧ xs.filterMap f = post := by
          simpa only [List.filterMap_cons,hx,List.nil_append,List.cons.injEq] using position
        exact ⟨[],x,xs,rfl,rfl,same.1 ▸ hx,same.2⟩
      | cons z zs =>
        have same : y = z ∧ xs.filterMap f = zs ++ e :: post := by
          simpa only [List.filterMap_cons,hx,List.cons_append,List.cons.injEq] using position
        obtain ⟨left,a,right,hs,hl,ha,hr⟩ := ih zs same.2
        exact ⟨x :: left,a,right,by simp only [hs,List.cons_append],
          by simp only [List.filterMap_cons,hx,hl,same.1],ha,hr⟩

theorem historyEvent_some (event : RxHistory.Event) (lower : RxJoint.Event)
    (mapped : historyEvent event = some lower) : event = RxHistory.promote lower := by
  cases event <;> simp only [historyEvent] at mapped
  all_goals try cases mapped
  case audit a =>
    cases a <;> cases mapped
    rfl
  all_goals rfl

/-- The RX projection drops routing events only; the lower linkage projection
drops precisely the existing non-linkage RX constructors. -/
theorem joint_position (h : List RoutingJoint.Event) (pre : List RxJoint.Event)
    (e : RxJoint.Event) (post : List RxJoint.Event)
    (position : (h.filterMap RoutingJoint.rxEvent).filterMap historyEvent = pre ++ e :: post) :
    ∃ left right, h = left ++ .rx (RxHistory.promote e) :: right ∧
      (left.filterMap RoutingJoint.rxEvent).filterMap historyEvent = pre ∧
      (right.filterMap RoutingJoint.rxEvent).filterMap historyEvent = post := by
  obtain ⟨rxPre,event,rxPost,rxPosition,preEq,eventEq,postEq⟩ :=
    filterMap_position historyEvent (h.filterMap RoutingJoint.rxEvent) pre e post position
  have eventValue := historyEvent_some event e eventEq
  subst event
  obtain ⟨left,joint,right,jointPosition,leftEq,jointEq,rightEq⟩ :=
    filterMap_position RoutingJoint.rxEvent h rxPre (RxHistory.promote e) rxPost rxPosition
  cases joint with
  | routing event => cases jointEq
  | rx event =>
    simp only [RoutingJoint.rxEvent,Option.some.injEq] at jointEq
    subst event
    exact ⟨left,right,jointPosition,leftEq ▸ preEq,rightEq ▸ postEq⟩

/-- The actual selected Stack entry has an earlier buffered entry and its
earlier consume in the same joint prefix. No uniqueness of values is needed. -/
theorem entered_position (linked : HistoryLinked (h.filterMap RoutingJoint.rxEvent))
    (position : h = pre ++ .rx (.entered e) :: post) :
    ∃ (receipt : RxDisposition.ConsumeReceipt), ∃ before between afterBuffer,
      pre = before ++ .rx (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) ::
        (between ++ .rx (.buffered e) :: afterBuffer) ∧
      e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes ∧
      Source e.tag.skb e.stamp receipt := by
  have entryLink := linked.at (pre := (pre.filterMap RoutingJoint.rxEvent).filterMap historyEvent)
    (e := RxJoint.Event.entered e)
    (post := (post.filterMap RoutingJoint.rxEvent).filterMap historyEvent)
    (by simp only [position,List.filterMap_append,List.filterMap_cons,RoutingJoint.rxEvent,
      historyEvent,List.nil_append])
  change Buffered [] ((pre.filterMap RoutingJoint.rxEvent).filterMap historyEvent) e at entryLink
  obtain ⟨a,b,buffered,consumed⟩ := entryLink
  simp only [List.nil_append,List.append_assoc,List.singleton_append] at buffered
  simp only [List.nil_append] at consumed
  obtain ⟨beforeBuffer,afterBuffer,bufferPosition,beforeEq,_⟩ := joint_position pre a (.buffered e) b buffered
  obtain ⟨receipt,c,d,origin,value,source,consumePosition,_⟩ := consumed
  simp only [List.nil_append,List.append_assoc,List.singleton_append] at consumePosition
  obtain ⟨before,between,consumePosition,_,_⟩ :=
    joint_position beforeBuffer c (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) d
      (beforeEq.trans consumePosition)
  refine ⟨receipt,before,between,afterBuffer,?_,origin,value,source⟩
  simpa only [RxHistory.promote,consumePosition,List.append_assoc,List.cons_append] using bufferPosition

end Leanux.Proofs.WG.Queues.RxLink
