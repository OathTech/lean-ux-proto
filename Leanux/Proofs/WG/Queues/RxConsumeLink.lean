import Leanux.Proofs.WG.Queues.RxPollDisposition

/-! Actual selected packets and ordered whole-receipt support. These are
separate invariants: old payload validity and completion contracts are unchanged.
No current packet residency is required after the consume call starts. -/
namespace Leanux.Proofs.WG.Queues.RxLink
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes RxJoint RxDisposition

/-- A source-linked receipt describes the selected cell at consume entry. -/
def Source (skb : SkbId) (stamp : PacketStamp) (r : ConsumeReceipt) : Prop :=
  r.Valid ∧ SelectedAt skb stamp r.packet r.run.before ∧ r.packet.peer = r.peer

/-- Strictly earlier, after this observation's actual incoming history. -/
def Before (base h : List RxJoint.Event) (e : RxJoint.Event) : Prop :=
  ∃ a b, h = base ++ a ++ [e] ++ b

def Consumed (base h : List RxJoint.Event) (e : Entry) : Prop :=
  ∃ r a b, e.origin = some r ∧ r.run.value = some e.tag.bytes ∧
    Source e.tag.skb e.stamp r ∧
    h = base ++ a ++ [.consumed e.tag.occurrence e.tag.skb e.stamp r] ++ b ∧
    ReadBeforeRemoval base (base ++ a) (e.tag.occurrence, e.tag.skb, e.stamp)

def Buffered (base h : List RxJoint.Event) (e : Entry) : Prop :=
  ∃ a b, h = base ++ a ++ [.buffered e] ++ b ∧ Consumed base (base ++ a) e

def Entered (base h : List RxJoint.Event) (e : Entry) : Prop :=
  ∃ a b, h = base ++ a ++ [.entered e] ++ b ∧ Buffered base (base ++ a) e

def EventLink (base h : List RxJoint.Event) : RxJoint.Event → Prop
  | .consumed n skb stamp r => Source skb stamp r ∧ ReadBeforeRemoval base h (n, skb, stamp)
  | .buffered e => Consumed base h e
  | .entered e => Buffered base h e
  | .completed e _ => Entered base h e
  | _ => True

/-- Only the newly appended events are constrained; arbitrary prior events
are not silently certified by a fresh poll. -/
inductive Linked (base : List RxJoint.Event) : List RxJoint.Event → Prop
  | start : Linked base base
  | snoc {h e} : Linked base h → EventLink base h e → Linked base (h ++ [e])

theorem Linked.extension (hi : Linked base h) : ∃ s, h = base ++ s := by
  induction hi with
  | start => exact ⟨[], by simp⟩
  | @snoc h e _ _ ih => obtain ⟨s, rfl⟩ := ih; exact ⟨s ++ [e], by simp only [List.append_assoc]⟩

theorem Before.append (hi : Before base h e) (t : List RxJoint.Event) : Before base (h ++ t) e := by
  obtain ⟨a, b, rfl⟩ := hi
  exact ⟨a, b ++ t, by simp only [List.append_assoc]⟩
theorem Consumed.append (hi : Consumed base h e) (t : List RxJoint.Event) : Consumed base (h ++ t) e := by
  obtain ⟨r, a, b, ho, hv, hs, he, hm⟩ := hi
  exact ⟨r, a, b ++ t, ho, hv, hs, by simp only [he, List.append_assoc], hm⟩
theorem Buffered.append (hi : Buffered base h e) (t : List RxJoint.Event) : Buffered base (h ++ t) e := by
  obtain ⟨a, b, he, hs⟩ := hi
  exact ⟨a, b ++ t, by simp only [he, List.append_assoc], hs⟩
theorem Entered.append (hi : Entered base h e) (t : List RxJoint.Event) : Entered base (h ++ t) e := by
  obtain ⟨a, b, he, hs⟩ := hi
  exact ⟨a, b ++ t, by simp only [he, List.append_assoc], hs⟩

theorem EventLink.append (hi : EventLink base h e) (t : List RxJoint.Event) : EventLink base (h ++ t) e := by
  cases e with
  | consumed n skb stamp r => exact ⟨hi.1, hi.2.append t⟩
  | buffered e => exact Consumed.append hi t
  | entered e => exact Buffered.append hi t
  | completed e r => exact Entered.append hi t
  | _ => trivial

/-- Every appended event has a strict prefix satisfying its own source link. -/
theorem Linked.events (hi : Linked base h) : ∃ s, h = base ++ s ∧
    ∀ e ∈ s, ∃ a b, s = a ++ [e] ++ b ∧ EventLink base (base ++ a) e := by
  induction hi with
  | start => exact ⟨[], by simp, by simp⟩
  | @snoc h e old he ih =>
    obtain ⟨s, hs, hall⟩ := ih
    refine ⟨s ++ [e], by simp only [hs, List.append_assoc], ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a,b,hab,hx⟩ := hall x hx
      exact ⟨a,b ++ [e],by simp only [hab,List.append_assoc],hx⟩
    · have hx : x = e := by simpa using hx
      subst x
      exact ⟨s,[],by simp,by simpa only [hs] using he⟩

theorem linked_emit (e : RxJoint.Event) :
    PrefixEnsures (fun h _ => Linked base h ∧ EventLink base h e) (Linked base)
      (emitPrefix e) (fun _ h _ => Linked base h) := by
  intro w h hi
  exact ⟨[e], rfl, hi.1.snoc hi.2, hi.1.snoc hi.2⟩

theorem linked_append_quiet (hi : Linked base h) (t : List RxJoint.Event)
    (ht : ∀ e ∈ t, ∀ pre, EventLink base pre e) : Linked base (h ++ t) := by
  induction t generalizing h with
  | nil => simpa using hi
  | cons e es ih =>
    have first := hi.snoc (ht e (by simp) h)
    simpa only [List.append_assoc, List.singleton_append] using
      ih first (fun x hx pre => ht x (List.mem_cons_of_mem _ hx) pre)

theorem linked_access (a : MixedM α) :
    PrefixPreserves (fun h _ => Linked base h) (Linked base) (access a) := by
  intro w h hi
  let t := ((runPrefix a w (h.filterMap accessEvent)).2.drop
    (h.filterMap accessEvent).length).map RxJoint.Event.access
  have hl : Linked base (h ++ t) := linked_append_quiet hi t (by
    intro e he pre
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp he
    trivial)
  refine ⟨t,rfl,hl,?_⟩
  cases (runPrefix (access a) w h).1 <;> trivial

theorem linked_lift (a : M α) :
    PrefixPreserves (fun h _ => Linked base h) (Linked base) (liftPrefix a) := by
  intro w h hi
  refine ⟨[],by simp,hi,?_⟩
  simp only [runPrefix_lift]
  cases a.run w <;> trivial

/-- Frame any monotone historical fact using the actual appended suffix. -/
theorem remember {F : List RxJoint.Event → Prop} (ha : PrefixEnsures P S a Q)
    (hm : ∀ h t, F h → F (h ++ t)) :
    PrefixEnsures (fun h w => P h w ∧ F h) S a (fun x h w => Q x h w ∧ F h) := by
  intro w h hi
  obtain ⟨s,he,hs,hq⟩ := ha w h hi.1
  refine ⟨s,he,hs,?_⟩
  cases hr : (runPrefix a w h).1 with
  | error e => trivial
  | ok out => exact ⟨by simpa only [hr] using hq, he ▸ hm h s hi.2⟩

def Supported (base h : List RxJoint.Event) (es : List Entry) : Prop := ∀ e ∈ es, Buffered base h e

theorem Supported.append (hi : Supported base h es) (t : List RxJoint.Event) : Supported base (h ++ t) es :=
  fun e he => (hi e he).append t

abbrev Context (base : List RxJoint.Event) (g : Gro) (h : List RxJoint.Event) (_ : World) :=
  Linked base h ∧ Supported base h (g.rxList ++ g.held)

theorem keep (a : Obs α) (ha : PrefixPreserves (fun h _ => Linked base h) (Linked base) a) :
    PrefixPreserves (Context base g) (Linked base) a :=
  remember (show PrefixEnsures _ _ a (fun _ h _ => Linked base h) from ha)
    (fun _ t hs => hs.append t)

theorem linked_receipt (a : Obs α) (f : RunWitness α → RxJoint.Event)
    (ha : PrefixPreserves (fun h _ => Linked base h) (Linked base) a)
    (hf : ∀ h r, EventLink base h (f r)) :
    PrefixPreserves (fun h _ => Linked base h) (Linked base) (receiptObserved a f) := by
  unfold receiptObserved
  change PrefixEnsures _ _ _ (fun _ h _ => Linked base h)
  apply PrefixEnsures.bind (show PrefixEnsures _ _ (captureObserved a)
    (fun _ h _ => Linked base h) from ha.captureObserved)
  intro r
  apply PrefixEnsures.bind
    ((linked_emit (f r)).consequence (fun h _ hi => ⟨hi,hf h r⟩) (fun _ _ _ hi => hi))
  intro _
  exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)

/-- The exact once-only consume run freezes the selected cell at its entry
World, before the operation can release it. Its outgoing access history hc is
followed by consumed, and only the Some arm then appends buffered. -/
theorem consume_link (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixEnsures (fun h w => Linked base h ∧ SelectedAt skb stamp pkt w ∧ pkt.peer = pid ∧
      ReadBeforeRemoval base h (n, skb, stamp)) (Linked base)
      (consume pid n skb stamp pkt ep)
      (fun out h _ => Linked base h ∧ Supported base h out.toList) := by
  intro w h hi
  obtain ⟨s,hs,hl,_⟩ := linked_access (base := base) (consumeDataDonePrefix pid pkt ep) w h hi.1
  have he := access_erases (consumeDataDonePrefix_erases pid pkt ep) w h
  rw [consume_run]
  cases hr : runPrefix (access (consumeDataDonePrefix pid pkt ep)) w h with
  | mk result hc =>
    simp only [hr] at hs hl he
    cases result with
    | error err => exact ⟨s,hs,hl,True.intro⟩
    | ok out =>
      rcases out with ⟨out,v⟩
      let r : ConsumeReceipt := ⟨pid,pkt,ep,⟨out,w,v⟩⟩
      have source : Source skb stamp r := ⟨he.symm,hi.2.1,hi.2.2.1⟩
      have removed : ReadBeforeRemoval base hc (n, skb, stamp) := hs ▸ hi.2.2.2.append s
      have consumed := hl.snoc (e := .consumed n skb stamp r) ⟨source,removed⟩
      cases out with
      | none => exact ⟨s ++ [.consumed n skb stamp r],by simp only [hs,List.append_assoc]; rfl,
          consumed,consumed,by simp [Supported]⟩
      | some bytes =>
        let e : Entry := ⟨⟨n,skb,bytes⟩,stamp,some r⟩
        obtain ⟨a,ha⟩ := hl.extension
        have support : Consumed base (hc ++ [.consumed n skb stamp r]) e :=
          ⟨r,a,[],rfl,rfl,source,by simp only [ha,List.append_nil]; rfl,by simpa only [ha] using removed⟩
        have buffered := consumed.snoc (e := .buffered e) support
        have eb : Buffered base ((hc ++ [.consumed n skb stamp r]) ++ [.buffered e]) e :=
          ⟨a ++ [.consumed n skb stamp r],[],by simp only [ha,List.append_assoc,List.append_nil],
            by simpa only [ha,List.append_assoc] using support⟩
        exact ⟨s ++ [.consumed n skb stamp r,.buffered e],by simp only [hs,List.append_assoc]; rfl,
          buffered,buffered,by simpa [Supported] using eb⟩

/-- Entering preserves the full buffered Entry; a completion is emitted only
by the unchanged once-only callback observer. -/
theorem enter_link (e : Entry) :
    PrefixEnsures (fun h _ => Linked base h ∧ Buffered base h e) (Linked base)
      (enter e) (fun _ h _ => Linked base h) := by
  have mark : PrefixEnsures (fun h _ => Linked base h ∧ Buffered base h e) (Linked base)
      (emitPrefix (.entered e)) (fun _ h _ => Linked base h ∧ Entered base h e) := by
    intro w h hi
    obtain ⟨s,hs⟩ := hi.1.extension
    have hl := hi.1.snoc (e := .entered e) hi.2
    exact ⟨[.entered e],rfl,hl,hl,s,[],by simp only [runPrefix_emit,hs,List.append_nil],by simpa only [hs] using hi.2⟩
  unfold enter receiptObserved
  apply PrefixEnsures.bind mark
  intro _
  have accessHeld := remember
    (show PrefixEnsures _ _ (access (stackReceivePrefix e.tag.bytes))
      (fun _ h _ => Linked base h) from linked_access _)
    (F := fun h => Entered base h e) (fun _ t hs => hs.append t)
  apply PrefixEnsures.bind (show PrefixEnsures (fun h _ => Linked base h ∧ Entered base h e)
    (Linked base) (captureObserved (access (stackReceivePrefix e.tag.bytes)))
    (fun _ h _ => Linked base h ∧ Entered base h e) from
    (show PrefixPreserves (fun h _ => Linked base h ∧ Entered base h e) (Linked base) _ from accessHeld).captureObserved)
  intro r
  apply PrefixEnsures.bind
    ((linked_emit (.completed e r)).consequence (fun _ _ hi => hi) (fun _ _ _ hi => hi))
  intro _
  exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)

theorem flush_link (es : List Entry) :
    PrefixEnsures (fun h _ => Linked base h ∧ Supported base h es) (Linked base)
      (flush es) (fun _ h _ => Linked base h) := by
  induction es with
  | nil => exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)
  | cons e es ih =>
    simp only [flush,List.forM_eq_forM,List.forM_cons]
    apply PrefixEnsures.bind
      ((remember (enter_link e) (F := fun h => Supported base h es)
        (fun _ t hi => hi.append t)).consequence
        (fun h w hi => ⟨⟨hi.1,hi.2 e (by simp)⟩,fun x hx => hi.2 x (List.mem_cons_of_mem _ hx)⟩)
        (fun _ _ _ hi => hi))
    intro _
    exact ih

theorem normalList_link (g : Gro) :
    PrefixEnsures (Context base g) (Linked base) (normalList g) (Context base) := by
  unfold normalList
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind
      ((remember (flush_link g.rxList) (F := fun h => Supported base h g.held)
        (fun _ t hi => hi.append t)).consequence
        (fun h w hi => ⟨⟨hi.1,fun e he => hi.2 e (List.mem_append_left _ he)⟩,
          fun e he => hi.2 e (List.mem_append_right _ he)⟩)
        (fun _ _ _ hi => hi))
    intro _
    exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => ⟨hi.1,by simpa using hi.2⟩)

theorem normalOne_link (g : Gro) (e : Entry) (n : Nat) :
    PrefixEnsures (fun h w => Context base g h w ∧ Buffered base h e) (Linked base)
      (normalOne g e n) (Context base) := by
  have transfer : ∀ h w, Context base g h w ∧ Buffered base h e →
      Context base {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + n} h w := by
    intro h w hi
    refine ⟨hi.1.1,?_⟩
    intro x hx
    simp only [List.mem_append,List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact hi.1.2 x (List.mem_append_left _ hx)
    · exact hi.2
    · exact hi.1.2 x (List.mem_append_right _ hx)
  unfold normalOne
  dsimp only
  split
  · exact (normalList_link _).consequence transfer (fun _ _ _ hi => hi)
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1.1) transfer

theorem receive_link (g : Gro) (e : Entry) :
    PrefixEnsures (fun h w => Context base g h w ∧ Buffered base h e) (Linked base)
      (receive g e) (Context base) := by
  unfold receive
  split
  · exact normalOne_link _ _ _
  · have transfer : ∀ h w, Context base g h w ∧ Buffered base h e →
        Context base {g with held := g.held ++ [e]} h w := by
      intro h w hi
      refine ⟨hi.1.1,?_⟩
      intro x hx
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hx | hx | rfl
      · exact hi.1.2 x (List.mem_append_left _ hx)
      · exact hi.1.2 x (List.mem_append_right _ hx)
      · exact hi.2
    split
    · apply PrefixEnsures.bind
        (remember (show PrefixEnsures _ _ (liftPrefix _) (fun _ => Context base g) from keep _ (linked_lift _))
          (F := fun h => Buffered base h e) (fun _ t hi => hi.append t))
      intro _
      exact PrefixEnsures.pure (fun _ _ hi => hi.1.1) transfer
    · exact PrefixEnsures.pure (fun _ _ hi => hi.1.1) transfer

theorem flushAll_link (g : Gro) :
    PrefixEnsures (Context base g) (Linked base) (flushAll g) (fun _ h _ => Linked base h) := by
  have loop : ∀ (es : List Entry) (cur : Gro), (∀ e ∈ es, e ∈ g.held) →
      PrefixEnsures (fun h w => Context base cur h w ∧ Supported base h g.held) (Linked base)
        (forIn es cur (fun e cur => do let out ← normalOne cur e 1; pure (.yield out)))
        (fun out h w => Context base out h w ∧ Supported base h g.held) := by
    intro es
    induction es with
    | nil => intro cur _; exact PrefixEnsures.pure (fun _ _ hi => hi.1.1) (fun _ _ hi => hi)
    | cons e es ih =>
      intro cur mem
      rw [List.forIn_cons]
      simp only [bind_assoc,pure_bind]
      apply PrefixEnsures.bind
        ((remember (normalOne_link cur e 1) (F := fun h => Supported base h g.held)
          (fun _ t hi => hi.append t)).consequence
          (fun h w hi => ⟨⟨hi.1,hi.2 e (mem e (by simp))⟩,hi.2⟩) (fun _ _ _ hi => hi))
      intro out
      exact ih out (fun x hx => mem x (List.mem_cons_of_mem _ hx))
  unfold flushAll
  apply PrefixEnsures.bind (Q := fun cur h w => Context base cur h w ∧ Supported base h g.held)
  · exact (loop g.held g (fun _ hi => hi)).consequence
      (fun h w hi => ⟨hi,fun e he => hi.2 e (List.mem_append_right _ he)⟩) (fun _ _ _ hi => hi)
  · intro cur
    apply PrefixEnsures.bind
      ((normalList_link {cur with held := []}).consequence
        (fun h w hi => ⟨hi.1.1,fun e he => hi.1.2 e (List.mem_append_left _ (by simpa using he))⟩)
        (fun _ _ _ hi => hi))
    intro _
    exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi.1)

/-- Rebase only the incoming journal prefix; all source Worlds and full
receipts remain the same. This is a pure witness translation, not an observer
history-neutrality assertion. -/
theorem read_rebase (hi : ReadBeforeRemoval base (base ++ s) k) (other : List RxJoint.Event) :
    ReadBeforeRemoval other (other ++ s) k := by
  obtain ⟨a,b,c,he⟩ := hi
  have hs : s = a ++ [readEvent k.2.1 k.2.2] ++ b ++ [.removed k.1 k.2.1 k.2.2] ++ c :=
    List.append_cancel_left (by simpa only [List.append_assoc] using he)
  exact ⟨a,b,c,by simp only [hs,List.append_assoc]⟩

theorem Consumed.rebase (hi : Consumed base (base ++ s) e) (other : List RxJoint.Event) :
    Consumed other (other ++ s) e := by
  obtain ⟨r,a,b,ho,hv,src,he,hr⟩ := hi
  have hs : s = a ++ [.consumed e.tag.occurrence e.tag.skb e.stamp r] ++ b :=
    List.append_cancel_left (by simpa only [List.append_assoc] using he)
  exact ⟨r,a,b,ho,hv,src,by simp only [hs,List.append_assoc],read_rebase hr other⟩

theorem Buffered.rebase (hi : Buffered base (base ++ s) e) (other : List RxJoint.Event) :
    Buffered other (other ++ s) e := by
  obtain ⟨a,b,he,hr⟩ := hi
  have hs : s = a ++ [.buffered e] ++ b :=
    List.append_cancel_left (by simpa only [List.append_assoc] using he)
  exact ⟨a,b,by simp only [hs,List.append_assoc],hr.rebase other⟩

theorem Entered.rebase (hi : Entered base (base ++ s) e) (other : List RxJoint.Event) :
    Entered other (other ++ s) e := by
  obtain ⟨a,b,he,hr⟩ := hi
  have hs : s = a ++ [.entered e] ++ b :=
    List.append_cancel_left (by simpa only [List.append_assoc] using he)
  exact ⟨a,b,by simp only [hs,List.append_assoc],hr.rebase other⟩

theorem EventLink.rebase (hi : EventLink base (base ++ s) e) (other : List RxJoint.Event) :
    EventLink other (other ++ s) e := by
  cases e with
  | consumed n skb stamp r => exact ⟨hi.1,read_rebase hi.2 other⟩
  | buffered e => exact Consumed.rebase hi other
  | entered e => exact Buffered.rebase hi other
  | completed e r => exact Entered.rebase hi other
  | _ => trivial

theorem Linked.rebase (hi : Linked base h) (other : List RxJoint.Event) :
    ∃ s, h = base ++ s ∧ Linked other (other ++ s) := by
  induction hi with
  | start => exact ⟨[],by simp,by simpa using (Linked.start (base := other))⟩
  | @snoc h e old he ih =>
    obtain ⟨s,hs,hl⟩ := ih
    refine ⟨s ++ [e],by simp only [hs,List.append_assoc],?_⟩
    have he' : EventLink base (base ++ s) e := hs ▸ he
    simpa only [List.append_assoc] using hl.snoc (he'.rebase other)

theorem read_forget_base (hi : ReadBeforeRemoval base h k) : ReadBeforeRemoval [] h k := by
  obtain ⟨a,b,c,he⟩ := hi
  exact ⟨base ++ a,b,c,by simpa only [List.nil_append,List.append_assoc] using he⟩

theorem Consumed.forget_base (hi : Consumed base h e) : Consumed [] h e := by
  obtain ⟨r,a,b,ho,hv,src,he,hr⟩ := hi
  exact ⟨r,base ++ a,b,ho,hv,src,by simpa only [List.nil_append] using he,
    by simpa only [List.nil_append] using read_forget_base hr⟩

theorem Buffered.forget_base (hi : Buffered base h e) : Buffered [] h e := by
  obtain ⟨a,b,he,hr⟩ := hi
  exact ⟨base ++ a,b,by simpa only [List.nil_append] using he,
    by simpa only [List.nil_append] using hr.forget_base⟩

theorem Entered.forget_base (hi : Entered base h e) : Entered [] h e := by
  obtain ⟨a,b,he,hr⟩ := hi
  exact ⟨base ++ a,b,by simpa only [List.nil_append] using he,
    by simpa only [List.nil_append] using hr.forget_base⟩

theorem EventLink.forget_base (hi : EventLink base h e) : EventLink [] h e := by
  cases e with
  | consumed n skb stamp r => exact ⟨hi.1,read_forget_base hi.2⟩
  | buffered e => exact Consumed.forget_base hi
  | entered e => exact Buffered.forget_base hi
  | completed e r => exact Entered.forget_base hi
  | _ => trivial

theorem Linked.join (old : Linked [] base) (hi : Linked base h) : Linked [] h := by
  induction hi with
  | start => exact old
  | snoc _ he ih => exact ih.snoc he.forget_base

theorem Linked.append (hi : Linked [] h) (ht : Linked [] t) : Linked [] (h ++ t) := by
  obtain ⟨s,hs,hl⟩ := ht.rebase h
  simp only [List.nil_append] at hs
  exact hi.join (hs ▸ hl)

end Leanux.Proofs.WG.Queues.RxLink
