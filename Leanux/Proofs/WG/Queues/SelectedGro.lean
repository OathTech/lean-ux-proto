import Leanux.Proofs.WG.Queues.RxPollGroOrder
import Leanux.Proofs.Logged.PrefixLoops

/-! Exact per-poll order follows GRO's held-entry transitions. An entry already
held may be completed before a refused same-flow offer is processed. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

structure GroAdvance (held : List GroEntry) (tail : List GroEntry → List GroEntry)
    (g : TaggedGro) (h : List GroEvent) : Prop where
  count : g.rxCount = g.rxList.length
  held : g.held = held
  order : ∀ future, selectedEntries (bufferedEntries h ++ future) =
    enteredEntries h ++ g.rxList ++ tail future

structure GroReady (g : TaggedGro) (h : List GroEvent) : Prop where
  count : g.rxCount = g.rxList.length
  heldSmall : g.held.length ≤ 1
  order : ∀ future, selectedEntries (bufferedEntries h ++ future) =
    enteredEntries h ++ g.rxList ++ selectWith g.held future

structure GroPending (g : TaggedGro) (out : Option GroEntry) (h : List GroEvent) : Prop where
  count : g.rxCount = g.rxList.length
  heldSmall : g.held.length ≤ 1
  order : ∀ future, selectedEntries (bufferedEntries h ++ future) =
    enteredEntries h ++ g.rxList ++ selectWith g.held (out.toList ++ future)

theorem GroAdvance.safe {held tail g h} (hi : GroAdvance held tail g h) : SelectedGroSafe h := by
  refine ⟨g.rxList ++ tail [], ?_⟩
  simpa only [List.append_nil, List.append_assoc] using hi.order []

theorem GroReady.safe {g h} (hi : GroReady g h) : SelectedGroSafe h := by
  refine ⟨g.rxList ++ g.held, ?_⟩
  simpa only [List.append_nil, selectWith, List.append_assoc] using hi.order []

theorem GroPending.safe {g out h} (hi : GroPending g out h) : SelectedGroSafe h := by
  refine ⟨g.rxList ++ selectWith g.held out.toList, ?_⟩
  simpa only [List.append_nil, List.append_assoc] using hi.order []

theorem GroReady.pending_none {g h} (hi : GroReady g h) : GroPending g none h :=
  ⟨hi.count, hi.heldSmall, by simpa using hi.order⟩

theorem GroPending.none_ready {g h} (hi : GroPending g none h) : GroReady g h :=
  ⟨hi.count, hi.heldSmall, by simpa using hi.order⟩

theorem GroAdvance.ready {held g h} (hi : GroAdvance held (selectWith held) g h)
    (hh : held.length ≤ 1) : GroReady g h := by
  exact ⟨hi.count, hi.held ▸ hh, by simpa only [hi.held] using hi.order⟩

@[simp] theorem buffered_append_entered (h : List GroEvent) (xs : List GroEntry) :
    bufferedEntries (h ++ xs.map GroEvent.entered) = bufferedEntries h := by
  have hn : xs.filterMap (fun _ => (none : Option GroEntry)) = [] := by
    induction xs <;> simp_all
  simp [bufferedEntries, List.filterMap_append, List.filterMap_map, Function.comp_def, hn]

@[simp] theorem entered_append_entered (h : List GroEvent) (xs : List GroEntry) :
    enteredEntries (h ++ xs.map GroEvent.entered) = enteredEntries h ++ xs := by
  simp [enteredEntries, List.filterMap_append, List.filterMap_map, Function.comp_def]

theorem GroReady.buffered {g h} (hi : GroReady g h) (e : GroEntry) :
    GroPending g (some e) (h ++ [.buffered e]) := by
  refine ⟨hi.count, hi.heldSmall, ?_⟩
  intro future
  simpa [bufferedEntries, enteredEntries, List.filterMap_append, List.append_assoc] using hi.order (e :: future)

theorem selected_lift (a : Leanux.M α) (I : List GroEvent → Prop)
    (hs : ∀ h, I h → SelectedGroSafe h) :
    PrefixEnsures (fun h _ => I h) SelectedGroSafe (liftPrefix a) (fun _ h _ => I h) :=
  PrefixEnsures.lift a (fun h _ => hs h) (fun _ _ _ _ hi _ => hi)

theorem dropGro_ready (pid occurrence id : Nat) (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (dropGroPrefix pid occurrence id)
      (fun _ h _ => GroReady g h) := by
  intro w h hi
  simp only [dropGroPrefix, runPrefix_bind, runPrefix_lift]
  cases (liftWG (dropRxQueue pid)).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨u, v⟩
    cases u
    have hh : GroReady g (h ++ [.removed occurrence id]) := by
      refine ⟨hi.count, hi.heldSmall, ?_⟩
      simpa [bufferedEntries, enteredEntries, List.filterMap_append] using hi.order
    exact ⟨[.removed occurrence id], rfl, hh.safe, hh⟩

theorem consumeGro_pending (pid occurrence id : Nat) (pkt : RxPacket)
    (endpoint : Endpoint) (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (consumeGro pid occurrence id pkt endpoint)
      (fun out h _ => GroPending g out h) := by
  intro w h hi
  rw [consumeGro_run]
  cases (liftWG (consumeDataDone pid pkt endpoint)).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨bytes, v⟩
    cases bytes with
    | none => exact ⟨[], by simp, hi.safe, hi.pending_none⟩
    | some bytes =>
      have hp := hi.buffered ⟨occurrence, id, bytes⟩
      exact ⟨[.buffered ⟨occurrence, id, bytes⟩], rfl, hp.safe, hp⟩

theorem flushGro_advance (g : TaggedGro) (held : List GroEntry) (tail : List GroEntry → List GroEntry) :
    PrefixEnsures (fun h _ => GroAdvance held tail g h) SelectedGroSafe (flushGro g.rxList)
      (fun _ h _ => GroAdvance held tail {g with rxList := [], rxCount := 0} h) := by
  intro w h hi
  obtain ⟨visited, remaining, he, hh, hok⟩ := flushGro_prefix g.rxList w h
  have hs : SelectedGroSafe (runPrefix (flushGro g.rxList) w h).2 := by
    refine ⟨remaining ++ tail [], ?_⟩
    rw [hh]
    change selectedEntries _ = _
    rw [buffered_append_entered, entered_append_entered]
    have ho := hi.order []
    simpa only [List.append_nil, he, List.append_assoc] using ho
  refine ⟨visited.map GroEvent.entered, hh, hs, ?_⟩
  cases hr : (runPrefix (flushGro g.rxList) w h).1 with
  | error e => trivial
  | ok out =>
    have hempty := hok out.1 out.2 hr
    have hv : g.rxList = visited := by simpa only [hempty, List.append_nil] using he
    rw [hh]
    refine ⟨rfl, hi.held, ?_⟩
    intro future
    simpa only [buffered_append_entered, entered_append_entered, List.append_nil, hv] using hi.order future

theorem groNormalList_advance (g : TaggedGro) (held : List GroEntry) (tail : List GroEntry → List GroEntry) :
    PrefixEnsures (fun h _ => GroAdvance held tail g h) SelectedGroSafe (groNormalListTagged g)
      (fun g' h _ => GroAdvance held tail g' h) := by
  unfold groNormalListTagged
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (flushGro_advance g held tail)
    intro u
    exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)

theorem groNormalOne_advance (g : TaggedGro) (e : GroEntry) (held : List GroEntry)
    (tail : List GroEntry → List GroEntry) :
    PrefixEnsures (fun h _ => GroAdvance held (fun future => e :: tail future) g h)
      SelectedGroSafe (groNormalOneTagged g e 1)
      (fun g' h _ => GroAdvance held tail g' h) := by
  have transfer {h} (hi : GroAdvance held (fun future => e :: tail future) g h) :
      GroAdvance held tail {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + 1} h := by
    refine ⟨by simp [hi.count], hi.held, ?_⟩
    intro future
    simpa only [List.append_assoc, List.singleton_append] using hi.order future
  unfold groNormalOneTagged
  dsimp only
  split
  · apply (groNormalList_advance _ held tail).consequence
    · intro h w hi; exact transfer hi
    · intro x h w hi; exact hi
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => transfer hi)

theorem flushGro_ready (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (flushGro g.rxList)
      (fun _ h _ => GroReady {g with rxList := [], rxCount := 0} h) := by
  intro w h hi
  have result := flushGro_advance g g.held (selectWith g.held) w h ⟨hi.count, rfl, hi.order⟩
  rcases result with ⟨events, append, safe, post⟩
  refine ⟨events, append, safe, ?_⟩
  cases hr : (runPrefix (flushGro g.rxList) w h).1 with
  | error err => trivial
  | ok out =>
    have hp : GroAdvance g.held (selectWith g.held) {g with rxList := [], rxCount := 0}
        (runPrefix (flushGro g.rxList) w h).2 := by simpa only [hr] using post
    exact hp.ready hi.heldSmall

theorem groNormalList_ready (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (groNormalListTagged g)
      (fun g' h _ => GroReady g' h) := by
  intro w h hi
  have result := groNormalList_advance g g.held (selectWith g.held) w h ⟨hi.count, rfl, hi.order⟩
  rcases result with ⟨events, append, safe, post⟩
  refine ⟨events, append, safe, ?_⟩
  cases hr : (runPrefix (groNormalListTagged g) w h).1 with
  | error err => trivial
  | ok out =>
    have hp : GroAdvance g.held (selectWith g.held) out.1
        (runPrefix (groNormalListTagged g) w h).2 := by simpa only [hr] using post
    exact hp.ready hi.heldSmall

theorem normal_selected (g : TaggedGro) (e : GroEntry)
    (choose : ∀ future, selectWith g.held (e :: future) = e :: selectWith g.held future) :
    PrefixEnsures (fun h _ => GroPending g (some e) h) SelectedGroSafe
      (groNormalOneTagged g e 1) (fun g' h _ => GroReady g' h) := by
  intro w h hi
  have ha : GroAdvance g.held (fun future => e :: selectWith g.held future) g h := by
    refine ⟨hi.count, rfl, ?_⟩
    intro future
    simpa only [Option.toList_some, List.singleton_append, choose] using hi.order future
  have result := groNormalOne_advance g e g.held (selectWith g.held) w h ha
  rcases result with ⟨events, append, safe, post⟩
  refine ⟨events, append, safe, ?_⟩
  cases hr : (runPrefix (groNormalOneTagged g e 1) w h).1 with
  | error err => trivial
  | ok out =>
    have hp : GroAdvance g.held (selectWith g.held) out.1 (runPrefix (groNormalOneTagged g e 1) w h).2 := by simpa only [hr] using post
    exact hp.ready hi.heldSmall

theorem refused_selected (g : TaggedGro) (old e : GroEntry) (flush : Bool)
    (choose : ∀ future, selectWith g.held (e :: future) =
      old :: (if flush then e :: selectWith [] future else selectWith [e] future)) :
    PrefixEnsures (fun h _ => GroPending g (some e) h) SelectedGroSafe
      (do let next ← groNormalOneTagged {g with held := []} old 1
          if flush then groNormalOneTagged next e 1 else pure {next with held := [e]})
      (fun g' h _ => GroReady g' h) := by
  apply PrefixEnsures.bind (Q := fun next h _ => GroAdvance []
    (fun future => if flush then e :: selectWith [] future else selectWith [e] future) next h)
  · apply (groNormalOne_advance _ old [] _).consequence
    · intro h w hi
      refine ⟨hi.count, rfl, ?_⟩
      intro future
      simpa only [Option.toList_some, List.singleton_append, choose] using hi.order future
    · intro next h w hi; exact hi
  · intro next
    cases flush with
    | false =>
      exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi =>
        ⟨hi.count, by simp, by simpa using hi.order⟩)
    | true =>
      apply (groNormalOne_advance next e [] (selectWith [])).consequence
      · intro h w hi; exact hi
      · intro out h w hi; exact hi.ready (by simp)

theorem held_selected (g : TaggedGro) (e : GroEntry) (empty : g.held = [])
    (choose : ∀ future, selectWith g.held (e :: future) = selectWith [e] future) :
    PrefixEnsures (fun h _ => GroPending g (some e) h) SelectedGroSafe
      (pure {g with held := g.held ++ [e]} : PrefixM GroEvent TaggedGro) (fun g' h _ => GroReady g' h) := by
  exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi =>
    ⟨hi.count, by simp [empty], by
      intro future
      have ho := hi.order future
      simp only [Option.toList_some, List.singleton_append] at ho
      rw [choose] at ho
      simpa only [empty, List.nil_append] using ho⟩)

theorem selected_stop (why : String) (g : TaggedGro) (e : GroEntry) :
    PrefixEnsures (fun h _ => GroPending g (some e) h) SelectedGroSafe
      (liftPrefix (unsupported why : Leanux.M TaggedGro)) (fun g' h _ => GroReady g' h) := by
  intro w h hi
  exact ⟨[], by simp [runPrefix_lift], hi.safe, True.intro⟩

theorem napiGroReceive_ready (g : TaggedGro) (e : GroEntry) :
    PrefixEnsures (fun h _ => GroPending g (some e) h) SelectedGroSafe (napiGroReceiveTagged g e)
      (fun g' h _ => GroReady g' h) := by
  cases hn : groNetwork e.bytes with
  | none =>
    simp only [napiGroReceiveTagged, hn]
    apply normal_selected
    intro future; simp only [selectWith, hn]
  | some net =>
    rcases net with ⟨off, lengthFlush⟩
    cases ht : groTcpHeader e.bytes off with
    | none =>
      simp only [napiGroReceiveTagged, hn, ht]
      apply normal_selected
      intro future; simp only [selectWith, hn, ht]
    | some tcp =>
      rcases tcp with ⟨thlen, len⟩
      rcases g with ⟨xs, count, held⟩
      cases held with
      | nil =>
        cases hf : lengthFlush || groFinalFlush (e.bytes.getD (off + 13) 0).toNat len <;>
          simp only [napiGroReceiveTagged, hn, ht, hf, Bool.false_eq_true, ↓reduceIte]
        · apply held_selected _ _ rfl
          intro future; simp only [selectWith, hn, ht, hf, Bool.false_eq_true, ↓reduceIte, List.nil_append]
        · apply normal_selected
          intro future; simp only [selectWith, hn, ht, hf, ↓reduceIte]
      | cons old rest =>
        cases rest with
        | nil =>
          cases hs : groSameFlow old.bytes e.bytes off
          · cases hf : lengthFlush || groFinalFlush (e.bytes.getD (off + 13) 0).toNat len <;>
              simp only [napiGroReceiveTagged, hn, ht, hs, hf, Bool.false_eq_true, ↓reduceIte]
            · exact selected_stop _ _ _
            · apply normal_selected
              intro future; simp only [selectWith, hn, ht, hs, hf, Bool.false_eq_true, ↓reduceIte]
          · cases hm : groMergeRefused old.bytes e.bytes off thlen len
            · simp only [napiGroReceiveTagged, hn, ht, hs, hm, Bool.not_false, ↓reduceIte]
              intro w h hi
              exact ⟨[], by change h = h ++ []; simp, hi.safe, True.intro⟩
            · simp only [napiGroReceiveTagged, hn, ht, hs, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              apply refused_selected
              intro future; simp only [selectWith, hn, ht, hs, hm, ↓reduceIte]
        | cons other rest =>
          intro w h hi
          have impossible := hi.heldSmall
          simp at impossible


/-- At most one held offer reaches the terminal flush. Expanding its actual
nil/singleton loop gives this complete action equality, including failed
callbacks, without using the stale intermediate held field as a remainder. -/
theorem napiGroFlushAllTagged_eq (g : TaggedGro)
    (hc : g.rxCount = g.rxList.length) (hh : g.held.length ≤ 1) :
    napiGroFlushAllTagged g = flushGro (g.rxList ++ g.held) := by
  rcases g with ⟨xs, count, held⟩
  dsimp only at hc hh ⊢
  subst count
  cases held with
  | nil =>
    cases xs with
    | nil => simp [napiGroFlushAllTagged, groNormalListTagged, flushGro, List.forM_eq_forM]
    | cons e xs => simp [napiGroFlushAllTagged, groNormalListTagged]
  | cons e tail =>
    have ht : tail = [] := by
      cases tail <;> simp_all
    subst tail
    simp only [napiGroFlushAllTagged, List.forIn_cons, List.forIn_nil]
    unfold groNormalOneTagged
    dsimp only
    split <;> simp [groNormalListTagged]

/-- Flush a specified next segment of selected entries. On failure the
visited prefix, including the failing callback entry, is retained. -/
theorem flushGro_selected (xs rest : List GroEntry) :
    PrefixEnsures (fun h _ => selectedEntries (bufferedEntries h) = enteredEntries h ++ xs ++ rest)
      SelectedGroSafe (flushGro xs)
      (fun _ h _ => selectedEntries (bufferedEntries h) = enteredEntries h ++ rest) := by
  intro w h hi
  obtain ⟨visited, remaining, he, hh, hok⟩ := flushGro_prefix xs w h
  have hs : SelectedGroSafe (runPrefix (flushGro xs) w h).2 := by
    refine ⟨remaining ++ rest, ?_⟩
    rw [hh]
    change selectedEntries _ = _
    rw [buffered_append_entered, entered_append_entered, hi, he]
    simp only [List.append_assoc]
  refine ⟨visited.map GroEvent.entered, hh, hs, ?_⟩
  cases hr : (runPrefix (flushGro xs) w h).1 with
  | error e => trivial
  | ok out =>
    rcases out with ⟨x, v⟩
    dsimp only
    have hempty := hok x v hr
    have hv : xs = visited := by simpa only [hempty, List.append_nil] using he
    rw [hh, buffered_append_entered, entered_append_entered]
    simpa only [hv, List.append_assoc] using hi

def GroComplete (h : List GroEvent) : Prop :=
  selectedEntries (bufferedEntries h) = enteredEntries h

theorem GroComplete.safe {h} (hi : GroComplete h) : SelectedGroSafe h :=
  ⟨[], by simpa [GroComplete] using hi⟩

theorem napiGroFlushAll_complete (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (napiGroFlushAllTagged g)
      (fun _ h _ => GroComplete h) := by
  intro w h hi
  rw [napiGroFlushAllTagged_eq g hi.count hi.heldSmall]
  have hf : PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe
      (flushGro (g.rxList ++ g.held)) (fun _ h _ => GroComplete h) := by
    apply (flushGro_selected (g.rxList ++ g.held) []).consequence
    · intro h _ hi
      simpa only [List.append_nil, selectWith, List.append_assoc] using hi.order []
    · intro _ _ _ hi
      simpa [GroComplete] using hi
  exact hf w h hi

theorem groOption_ready (g : TaggedGro) (out : Option GroEntry) :
    PrefixEnsures (fun h _ => GroPending g out h) SelectedGroSafe
      (forIn out.toList g (fun e g => do
        let g' ← napiGroReceiveTagged g e
        pure (.yield g')))
      (fun g' h _ => GroReady g' h) := by
  cases out with
  | none =>
    exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi.none_ready)
  | some e =>
    simpa [List.forIn_cons, List.forIn_nil, bind_assoc] using napiGroReceive_ready g e

theorem ready_lift_bind (a : Leanux.M α) (g : TaggedGro) (f : α → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (f x) Q) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (liftPrefix a >>= f) Q :=
  PrefixEnsures.bind (selected_lift a (GroReady g) (fun _ hi => hi.safe)) hf

theorem ready_drop_bind (pid occurrence id : Nat) (g : TaggedGro)
    (f : Unit → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (f x) Q) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (dropGroPrefix pid occurrence id >>= f) Q :=
  PrefixEnsures.bind (dropGro_ready pid occurrence id g) hf

theorem ready_consume_bind (pid occurrence id : Nat) (pkt : RxPacket) (endpoint : Endpoint)
    (g : TaggedGro) (f : Option GroEntry → PrefixM GroEvent β)
    (hf : ∀ out, PrefixEnsures (fun h _ => GroPending g out h) SelectedGroSafe (f out) Q) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe
      (consumeGro pid occurrence id pkt endpoint >>= f) Q :=
  PrefixEnsures.bind (consumeGro_pending pid occurrence id pkt endpoint g) hf

theorem pending_option_bind (g : TaggedGro) (out : Option GroEntry)
    (f : TaggedGro → PrefixM GroEvent β)
    (hf : ∀ g', PrefixEnsures (fun h _ => GroReady g' h) SelectedGroSafe (f g') Q) :
    PrefixEnsures (fun h _ => GroPending g out h) SelectedGroSafe
      ((forIn out.toList g (fun e g => do let g' ← napiGroReceiveTagged g e; pure (.yield g'))) >>= f) Q :=
  PrefixEnsures.bind (groOption_ready g out) hf

theorem ready_flush_bind (g : TaggedGro) (f : Unit → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => GroComplete h) SelectedGroSafe (f x) Q) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (napiGroFlushAllTagged g >>= f) Q :=
  PrefixEnsures.bind (napiGroFlushAll_complete g) hf

theorem selected_unsupported_bind (why : String) (f : Unit → PrefixM GroEvent α)
    (hs : ∀ h w, P h w → SelectedGroSafe h) :
    PrefixEnsures P SelectedGroSafe (liftPrefix (unsupported why) >>= f) Q := by
  intro w h hi
  refine ⟨[], ?_, ?_, ?_⟩
  · change h = h ++ []; simp
  · change SelectedGroSafe h; exact hs h w hi
  · change True; trivial

theorem selected_invariant_bind (why : String) (f : Unit → PrefixM GroEvent α)
    (hs : ∀ h w, P h w → SelectedGroSafe h) :
    PrefixEnsures P SelectedGroSafe (liftPrefix (invariant why) >>= f) Q := by
  intro w h hi
  refine ⟨[], ?_, ?_, ?_⟩
  · change h = h ++ []; simp
  · change SelectedGroSafe h; exact hs h w hi
  · change True; trivial

theorem GroReady.empty_complete {h} (hi : GroReady {} h) : GroComplete h := by
  simpa only [GroComplete, List.append_nil, selectWith, List.append_assoc] using hi.order []

/-- One complete poll preserves selected callback-prefix order on all inputs,
including every Stop. Successful completion enters every buffered offer in
that selected order. No property of the input World or receive queue is used. -/
theorem rxPollGro_selected_spec (pid : PeerId) (budget : Nat) :
    PrefixEnsures (fun h _ => GroReady {} h) SelectedGroSafe (rxPollGro pid budget)
      (fun _ h _ => GroComplete h) := by
  unfold rxPollGro
  apply ready_lift_bind
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi.empty_complete)
  · apply PrefixEnsures.bind (Q := fun acc : Nat × TaggedGro × Bool => fun h _ => GroReady acc.2.1 h)
    · with_reducible apply (PrefixEnsures.rangeInvariant _ (0, ({} : TaggedGro), false) _
        (fun acc : Nat × TaggedGro × Bool => fun h _ => GroReady acc.2.1 h) SelectedGroSafe
        (fun _ _ _ hi => hi.safe))
      intro index acc
      repeat' first
        | exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
        | with_reducible apply selected_invariant_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply selected_unsupported_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply ready_drop_bind
        | with_reducible apply ready_consume_bind
        | with_reducible apply pending_option_bind
        | with_reducible apply ready_lift_bind
        | with_reducible apply PrefixEnsures.ite
        | (with_reducible intro x; try dsimp only)
        | (with_reducible split)
    · intro acc
      repeat' first
        | exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
        | with_reducible apply selected_invariant_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply selected_unsupported_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply ready_flush_bind
        | with_reducible apply ready_lift_bind
        | with_reducible apply PrefixEnsures.ite
        | (with_reducible intro x; try dsimp only)
        | (with_reducible split)

theorem groReady_initial : GroReady {} [] := by
  exact ⟨rfl, by simp, fun _ => rfl⟩

theorem rxPollGro_selected_prefix (pid : PeerId) (budget : Nat) (w : World) :
    SelectedGroSafe (runPrefix (rxPollGro pid budget) w []).2 :=
  (rxPollGro_selected_spec pid budget w [] groReady_initial).choose_spec.2.1

theorem rxPollGro_selected_complete (pid : PeerId) (budget : Nat) (w v : World) (n : Nat)
    (hr : (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)).run w = .ok (n, v)) :
    GroComplete (runPrefix (rxPollGro pid budget) w []).2 := by
  have hs := (rxPollGro_selected_spec pid budget w [] groReady_initial).choose_spec.2.2
  have ho := (rxPollGro_erases pid budget w []).trans hr
  simpa only [ho] using hs

end Leanux.Proofs.WG.Queues
