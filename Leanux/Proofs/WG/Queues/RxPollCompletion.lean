import Leanux.Proofs.WG.Queues.RxPollComposition

/-! Ordered callback entry/return pairing, independent of allocation and queue
invariants. A receipt witnesses the actual normal Stack return; it says nothing
about socket inbox arrival or the disposition of other receive-pipeline items. -/
namespace Leanux.Proofs.WG.Queues.RxCompletion
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Lifetimes

inductive Step where
  | entered (entry : RxJoint.Entry)
  | completed (entry : RxJoint.Entry) (witness : RunWitness Unit)

/-- Exact adjacent entry/return pairs after unrelated journal events are erased.
Each return carries the actual original Stack execution equation. -/
inductive ClosedTrace : List Step → Prop where
  | nil : ClosedTrace []
  | pair (e : RxJoint.Entry) (r : RunWitness Unit)
      (valid : r.Valid (Stack.receive e.tag.bytes)) {tail : List Step}
      (rest : ClosedTrace tail) :
      ClosedTrace (.entered e :: .completed e r :: tail)

/-- Failure can leave precisely one final entry unmatched, after complete pairs. -/
def PrefixTrace (t : List Step) : Prop :=
  ClosedTrace t ∨ ∃ pre e, ClosedTrace pre ∧ t = pre ++ [.entered e]

theorem ClosedTrace.prefix (h : ClosedTrace t) : PrefixTrace t := Or.inl h

theorem ClosedTrace.append (ha : ClosedTrace a) (hb : ClosedTrace b) : ClosedTrace (a ++ b) := by
  induction ha with
  | nil => exact hb
  | pair e r valid rest ih => exact .pair e r valid ih

theorem ClosedTrace.append_prefix (ha : ClosedTrace a) (hb : PrefixTrace b) : PrefixTrace (a ++ b) := by
  rcases hb with closed | ⟨pre, e, closed, rfl⟩
  · exact (ha.append closed).prefix
  · exact Or.inr ⟨a ++ pre, e, ha.append closed, by simp [List.append_assoc]⟩

def entered : Step → Option RxJoint.Entry | .entered e => some e | _ => none
def completed : Step → Option RxJoint.Entry | .completed e _ => some e | _ => none

theorem ClosedTrace.matches (ht : ClosedTrace t) : t.filterMap entered = t.filterMap completed := by
  induction ht with
  | nil => rfl
  | pair e r valid rest ih => simpa only [List.filterMap_cons, entered, completed] using congrArg (e :: ·) ih

theorem ClosedTrace.receipts (ht : ClosedTrace t) :
    ∀ e r, Step.completed e r ∈ t → r.Valid (Stack.receive e.tag.bytes) := by
  induction ht with
  | nil => simp
  | pair e r valid rest ih =>
    intro x s hm
    simp only [List.mem_cons] at hm
    rcases hm with bad | eq | hm
    · cases bad
    · cases eq; exact valid
    · exact ih x s hm

def jointEvent : RxJoint.Event → Option Step
  | .entered e => some (.entered e)
  | .completed e r => some (.completed e r)
  | _ => none

def historyEvent : RxHistory.Event → Option Step
  | .entered e => some (.entered e)
  | .completed e r => some (.completed e r)
  | _ => none

/-- The protocol's entries are exactly the pre-existing stamped entry journal. -/
theorem joint_entries (h : List RxJoint.Event) :
    (h.filterMap jointEvent).filterMap entered = RxJoint.entries h := by
  unfold RxJoint.entries
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> first | exact ih | exact congrArg (List.cons _) ih

theorem history_entries (h : List RxHistory.Event) :
    (h.filterMap historyEvent).filterMap entered = RxHistory.entries h := by
  unfold RxHistory.entries
  induction h with
  | nil => rfl
  | cons e h ih => cases e <;> first | exact ih | exact congrArg (List.cons _) ih

def Closed (ρ : E → Option Step) (h : List E) : Prop := ClosedTrace (h.filterMap ρ)
def CompletionPrefix (ρ : E → Option Step) (h : List E) : Prop := PrefixTrace (h.filterMap ρ)
abbrev Preserves (ρ : E → Option Step) (a : PrefixM E α) :=
  PrefixPreserves (fun h _ => Closed ρ h) (CompletionPrefix ρ) a

theorem Closed.prefix (h : Closed ρ t) : CompletionPrefix ρ t := ClosedTrace.prefix h

theorem quiet (hf : HistoryFrame ρ a) (ha : Appends a) : Preserves ρ a := by
  intro w h hi
  obtain ⟨s, hs⟩ := ha w h
  have hc : Closed ρ (runPrefix a w h).2 := by simpa only [Closed, hf w h] using hi
  refine ⟨s, hs, hc.prefix, ?_⟩
  cases (runPrefix a w h).1 <;> simp_all

theorem access_quiet (a : MixedM α) : Preserves jointEvent (RxJoint.access a) :=
  quiet (fun w h => focusPrefix_other RxJoint.Event.access RxJoint.accessEvent jointEvent
    (fun _ => rfl) a w h) (RxJoint.access_appends a)

theorem lift_quiet (a : M α) : Preserves ρ (liftPrefix a) :=
  quiet (HistoryFrame.lift _ _) (Appends.lift _)

theorem emit_quiet (e : E) (he : ρ e = none) : Preserves ρ (emitPrefix e) :=
  quiet (HistoryFrame.emit _ he) (fun _ _ => ⟨[e], rfl⟩)

/-- Literal once-only execution: entry before the original callback, receipt
only after its actual normal return, exact failed journal otherwise. -/
theorem enter_run (e : RxJoint.Entry) (w : World) (h : List RxJoint.Event) :
    runPrefix (RxJoint.enter e) w h =
      match runPrefix (RxJoint.access (stackReceivePrefix e.tag.bytes)) w (h ++ [.entered e]) with
      | (.error stop, t) => (.error stop, t)
      | (.ok (x, v), t) => (.ok (x, v), t ++ [.completed e ⟨x, w, v⟩]) := by
  unfold RxJoint.enter
  simp only [runPrefix_bind, runPrefix_emit, runPrefix_receiptObserved]
  cases runPrefix (RxJoint.access (stackReceivePrefix e.tag.bytes)) w (h ++ [.entered e]) with
  | mk out t => cases out <;> rfl

theorem enter_erases (e : RxJoint.Entry) :
    ErasesPrefix (RxJoint.enter e) (Stack.receive e.tag.bytes) := by
  intro w h
  have he := RxJoint.access_erases (stackReceivePrefix_erases e.tag.bytes) w (h ++ [.entered e])
  rw [enter_run]
  cases hr : runPrefix (RxJoint.access (stackReceivePrefix e.tag.bytes)) w (h ++ [.entered e]) with
  | mk out t => cases out <;> simpa only [hr] using he

/-- Normal return exposes matching ordered entry/receipt lists and validates
all receipts against their own captured original callback Worlds. -/
theorem normal_receipts {E α : Type} {ρ : E → Option Step} {a : PrefixM E α}
    (ha : Preserves ρ a) (w : World) (h : List E)
    (hi : Closed ρ h) (x : α) (v : World)
    (hr : (runPrefix a w h).1 = .ok (x, v)) :
    let t := (runPrefix a w h).2.filterMap ρ
    t.filterMap entered = t.filterMap completed ∧
      ∀ e r, Step.completed e r ∈ t → r.Valid (Stack.receive e.tag.bytes) := by
  have hc := (ha w h hi).choose_spec.2.2
  rw [hr] at hc
  exact ⟨ClosedTrace.matches hc, ClosedTrace.receipts hc⟩

theorem enter_preserves (e : RxJoint.Entry) : Preserves jointEvent (RxJoint.enter e) := by
  intro w h hi
  obtain ⟨s, hs⟩ := RxJoint.access_appends (stackReceivePrefix e.tag.bytes) w (h ++ [.entered e])
  have hf := focusPrefix_other RxJoint.Event.access RxJoint.accessEvent jointEvent
    (fun _ => rfl) (stackReceivePrefix e.tag.bytes) w (h ++ [RxJoint.Event.entered e])
  change (runPrefix (RxJoint.access (stackReceivePrefix e.tag.bytes)) w (h ++ [.entered e])).2.filterMap jointEvent =
    (h ++ [RxJoint.Event.entered e]).filterMap jointEvent at hf
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, jointEvent] at hf
  have he := RxJoint.access_erases (stackReceivePrefix_erases e.tag.bytes) w (h ++ [.entered e])
  cases hr : runPrefix (RxJoint.access (stackReceivePrefix e.tag.bytes)) w (h ++ [.entered e]) with
  | mk out t =>
    simp only [hr] at hs hf he
    change t = (h ++ [.entered e]) ++ s at hs
    change t.filterMap jointEvent = h.filterMap jointEvent ++ [.entered e] at hf
    cases out with
    | error stop =>
      refine ⟨[.entered e] ++ s, ?_, ?_, ?_⟩
      · simpa only [enter_run, hr, List.append_assoc] using hs
      · change PrefixTrace ((runPrefix (RxJoint.enter e) w h).2.filterMap jointEvent)
        rw [enter_run, hr]
        exact Or.inr ⟨h.filterMap jointEvent, e, hi, hf⟩
      · simp only [enter_run, hr]
    | ok out =>
      rcases out with ⟨x, v⟩
      have hv : RunWitness.Valid (Stack.receive e.tag.bytes) ⟨x, w, v⟩ := by
        change (Stack.receive e.tag.bytes).run w = .ok (x, v)
        exact he.symm
      have hc : Closed jointEvent (t ++ [.completed e ⟨x, w, v⟩]) := by
        unfold Closed
        simp only [List.filterMap_append, hf, List.filterMap_cons, List.filterMap_nil, jointEvent]
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using ClosedTrace.append hi (ClosedTrace.pair e ⟨x, w, v⟩ hv .nil)
      refine ⟨[.entered e] ++ s ++ [.completed e ⟨x, w, v⟩], ?_, ?_, ?_⟩
      · simp only [enter_run, hr, hs, List.append_assoc]
      · simpa only [enter_run, hr] using hc.prefix
      · simpa only [enter_run, hr] using hc

theorem flush_preserves (es : List RxJoint.Entry) : Preserves jointEvent (RxJoint.flush es) :=
  PrefixPreserves.forM es RxJoint.enter (fun _ _ hi => hi.prefix) enter_preserves

theorem normalList_preserves (g : RxJoint.Gro) : Preserves jointEvent (RxJoint.normalList g) := by
  unfold RxJoint.normalList
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.prefix) _
  · exact (flush_preserves _).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.prefix) _)

theorem normalOne_preserves (g : RxJoint.Gro) (e : RxJoint.Entry) (n : Nat) :
    Preserves jointEvent (RxJoint.normalOne g e n) := by
  unfold RxJoint.normalOne
  dsimp only
  split
  · exact normalList_preserves _
  · exact PrefixPreserves.pure (fun _ _ hi => hi.prefix) _

theorem receive_preserves (g : RxJoint.Gro) (e : RxJoint.Entry) :
    Preserves jointEvent (RxJoint.receive g e) := by
  unfold RxJoint.receive
  split
  · exact normalOne_preserves _ _ _
  · split
    · exact (lift_quiet _).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.prefix) _)
    · exact PrefixPreserves.pure (fun _ _ hi => hi.prefix) _

theorem flushAll_preserves (g : RxJoint.Gro) : Preserves jointEvent (RxJoint.flushAll g) := by
  unfold RxJoint.flushAll
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn
    · exact fun _ _ hi => hi.prefix
    · intro e g
      exact (normalOne_preserves g e 1).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.prefix) _)
  · intro g
    exact (normalList_preserves _).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.prefix) _)

theorem capture_quiet (skb : SkbId) : Preserves jointEvent (RxJoint.capture skb) := by
  apply quiet ?_ (RxJoint.capture_appends skb)
  intro w h
  rw [RxJoint.capture_run]
  cases (getRxSkb skb).run w <;> simp [List.filterMap_append, jointEvent]

theorem consume_quiet (pid n skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    Preserves jointEvent (RxJoint.consume pid n skb stamp pkt ep) := by
  unfold RxJoint.consume
  apply PrefixPreserves.bind (access_quiet _)
  intro out
  cases out with
  | none => exact PrefixPreserves.pure (fun _ _ hi => hi.prefix) _
  | some bytes => exact (emit_quiet _ rfl).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.prefix) _)

/-- No allocation, residency, progress or success premise is needed for the
protocol: all complete callback pairs are ordered, and a Stop can leave one
trailing entry. A normal poll return closes every callback it entered. -/
theorem poll_preserves (pid : PeerId) (budget : Nat) : Preserves jointEvent (RxJoint.poll pid budget) := by
  unfold RxJoint.poll RxJoint.drop
  repeat' first
    | with_reducible exact capture_quiet _
    | with_reducible exact consume_quiet _ _ _ _ _ _
    | with_reducible exact receive_preserves _ _
    | with_reducible exact flushAll_preserves _
    | with_reducible exact access_quiet _
    | with_reducible exact emit_quiet _ rfl
    | with_reducible exact lift_quiet _
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.prefix) _
    | with_reducible apply PrefixPreserves.range
    | with_reducible apply PrefixPreserves.forIn
    | with_reducible apply PrefixPreserves.bind
    | exact fun _ _ hi => hi.prefix
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem seed_empty (prior : List LifetimeEvent) :
    (RxJoint.seed prior).filterMap jointEvent = [] :=
  filterMap_disjoint RxJoint.Event.access jointEvent (fun _ => rfl) prior

theorem promote_protocol (suffix : List RxJoint.Event) :
    (suffix.map RxHistory.promote).filterMap historyEvent = suffix.filterMap jointEvent := by
  induction suffix with
  | nil => rfl
  | cons e s ih => cases e <;> simp only [List.map_cons, List.filterMap_cons,
      RxHistory.promote, historyEvent, jointEvent, ih]

/-- Promote only the newly appended local suffix; the local audit seed is the
exact existing lifetime history, including its interleaved probe projection. -/
theorem observePoll_preserves (pid : PeerId) (budget : Nat) :
    Preserves historyEvent (RxHistory.observePoll pid budget) := by
  intro w h hi
  obtain ⟨s, hs, hp, hn⟩ := poll_preserves pid budget w (RxJoint.seed (RxHistory.prior h))
    (by simp only [Closed, seed_empty]; exact ClosedTrace.nil)
  have hg := RxHistory.observePoll_suffix pid budget w h _ s (Prod.ext rfl hs)
  have ht : (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).2.filterMap jointEvent =
      s.filterMap jointEvent := by rw [hs, List.filterMap_append, seed_empty, List.nil_append]
  have hp' : PrefixTrace (s.filterMap jointEvent) := by simpa only [CompletionPrefix, ht] using hp
  refine ⟨s.map RxHistory.promote, by rw [hg], ?_, ?_⟩
  · change PrefixTrace ((runPrefix (RxHistory.observePoll pid budget) w h).2.filterMap historyEvent)
    rw [hg, List.filterMap_append, promote_protocol]
    exact ClosedTrace.append_prefix hi hp'
  · rw [hg]
    cases hr : (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).1 with
    | error stop => trivial
    | ok out =>
      have hc : ClosedTrace (s.filterMap jointEvent) := by simpa only [hr, Closed, ht] using hn
      change ClosedTrace ((h ++ s.map RxHistory.promote).filterMap historyEvent)
      rw [List.filterMap_append, promote_protocol]
      exact ClosedTrace.append hi hc

/-- A finite sequence of actual observed polls closes all callbacks on normal
return. Failure retains complete pairs followed by at most one unfinished entry. -/
theorem polls_preserves (calls : List (PeerId × Nat)) : Preserves historyEvent (RxHistory.polls calls) := by
  unfold RxHistory.polls
  apply PrefixPreserves.forM
  · exact fun _ _ hi => hi.prefix
  · intro call
    exact (observePoll_preserves call.1 call.2).bind
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.prefix) _)

end Leanux.Proofs.WG.Queues.RxCompletion
