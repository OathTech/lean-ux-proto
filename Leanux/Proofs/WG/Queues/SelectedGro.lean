import Leanux.Proofs.WG.Queues.RxPollGroOrder
import Leanux.Proofs.Logged.PrefixLoops

/-! Per-poll order selected by original normal/held GRO batching. The observer
and chronological predicate remain unchanged. State invariants are derived
inside a poll beginning with empty history, independently of its input World. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

def normalEntries (xs : List GroEntry) : List GroEntry :=
  xs.filter (fun e => groTakenAtOnce e.bytes)

def heldEntries (xs : List GroEntry) : List GroEntry :=
  xs.filter (fun e => !groTakenAtOnce e.bytes)

def selectedEntries (xs : List GroEntry) : List GroEntry :=
  normalEntries xs ++ heldEntries xs

structure GroReady (g : TaggedGro) (h : List GroEvent) : Prop where
  count : g.rxCount = g.rxList.length
  heldSmall : g.held.length ≤ 1
  normal : normalEntries (bufferedEntries h) = enteredEntries h ++ g.rxList
  held : heldEntries (bufferedEntries h) = g.held

structure GroPending (g : TaggedGro) (out : Option GroEntry) (h : List GroEvent) : Prop where
  count : g.rxCount = g.rxList.length
  heldSmall : g.held.length ≤ 1
  normal : normalEntries (bufferedEntries h) =
    enteredEntries h ++ g.rxList ++ normalEntries out.toList
  held : heldEntries (bufferedEntries h) = g.held ++ heldEntries out.toList

theorem GroReady.safe {g h} (hi : GroReady g h) : SelectedGroSafe h := by
  refine ⟨g.rxList ++ g.held, ?_⟩
  change normalEntries _ ++ heldEntries _ = _
  rw [hi.normal, hi.held, List.append_assoc]

theorem GroPending.safe {g out h} (hi : GroPending g out h) : SelectedGroSafe h := by
  refine ⟨g.rxList ++ normalEntries out.toList ++ g.held ++ heldEntries out.toList, ?_⟩
  change normalEntries _ ++ heldEntries _ = _
  rw [hi.normal, hi.held]
  simp only [List.append_assoc]

theorem GroReady.pending_none {g h} (hi : GroReady g h) : GroPending g none h := by
  exact ⟨hi.count, hi.heldSmall, by simpa [normalEntries] using hi.normal,
    by simpa [heldEntries] using hi.held⟩

theorem GroPending.none_ready {g h} (hi : GroPending g none h) : GroReady g h := by
  exact ⟨hi.count, hi.heldSmall, by simpa [normalEntries] using hi.normal,
    by simpa [heldEntries] using hi.held⟩

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
  refine ⟨hi.count, hi.heldSmall, ?_, ?_⟩
  · simpa [bufferedEntries, enteredEntries, normalEntries, List.filterMap_append,
      List.filter_append, List.append_assoc] using congrArg (· ++ normalEntries [e]) hi.normal
  · simpa [bufferedEntries, heldEntries, List.filterMap_append, List.filter_append] using
      congrArg (· ++ heldEntries [e]) hi.held

theorem selected_lift (a : M α) (I : List GroEvent → Prop)
    (hs : ∀ h, I h → SelectedGroSafe h) :
    PrefixEnsures (fun h _ => I h) SelectedGroSafe (liftPrefix a) (fun _ h _ => I h) :=
  PrefixEnsures.lift a (fun h _ => hs h) (fun _ _ _ _ hi _ => hi)

theorem dropGro_ready (pid occurrence id : Nat) (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (dropGroPrefix pid occurrence id)
      (fun _ h _ => GroReady g h) := by
  intro w h hi
  simp only [dropGroPrefix, runPrefix_bind, runPrefix_lift]
  cases (dropRxQueue pid).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨u, v⟩
    cases u
    have hh : GroReady g (h ++ [.removed occurrence id]) := by
      refine ⟨hi.count, hi.heldSmall, ?_, ?_⟩
      · simpa [bufferedEntries, enteredEntries, List.filterMap_append] using hi.normal
      · simpa [bufferedEntries, List.filterMap_append] using hi.held
    exact ⟨[.removed occurrence id], rfl, hh.safe, hh⟩

theorem consumeGro_pending (pid occurrence id : Nat) (pkt : RxPacket)
    (endpoint : Endpoint) (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (consumeGro pid occurrence id pkt endpoint)
      (fun out h _ => GroPending g out h) := by
  intro w h hi
  rw [consumeGro_run]
  cases (consumeDataDone pid pkt endpoint).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨bytes, v⟩
    cases bytes with
    | none => exact ⟨[], by simp, hi.safe, hi.pending_none⟩
    | some bytes =>
      have hp := hi.buffered ⟨occurrence, id, bytes⟩
      exact ⟨[.buffered ⟨occurrence, id, bytes⟩], rfl, hp.safe, hp⟩

theorem flushGro_ready (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (flushGro g.rxList)
      (fun _ h _ => GroReady {g with rxList := [], rxCount := 0} h) := by
  intro w h hi
  obtain ⟨visited, remaining, he, hh, hok⟩ := flushGro_prefix g.rxList w h
  have hs : SelectedGroSafe (runPrefix (flushGro g.rxList) w h).2 := by
    refine ⟨remaining ++ g.held, ?_⟩
    rw [hh]
    change normalEntries _ ++ heldEntries _ = _
    rw [buffered_append_entered, entered_append_entered, hi.normal, hi.held, he]
    simp only [List.append_assoc]
  refine ⟨visited.map GroEvent.entered, hh, hs, ?_⟩
  cases hr : (runPrefix (flushGro g.rxList) w h).1 with
  | error e => trivial
  | ok out =>
    have hempty := hok out.1 out.2 hr
    have hv : g.rxList = visited := by simpa only [hempty, List.append_nil] using he
    rw [hh]
    refine ⟨rfl, hi.heldSmall, ?_, ?_⟩
    · simpa only [buffered_append_entered, entered_append_entered, List.append_nil, hv] using hi.normal
    · simpa only [buffered_append_entered] using hi.held

theorem groNormalList_ready (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (groNormalListTagged g)
      (fun g' h _ => GroReady g' h) := by
  unfold groNormalListTagged
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (flushGro_ready g)
    intro u
    exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)

theorem GroPending.normal_ready {g h e} (hi : GroPending g (some e) h)
    (hn : groTakenAtOnce e.bytes = true) :
    GroReady {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + 1} h := by
  refine ⟨by simp [hi.count], hi.heldSmall, ?_, ?_⟩
  · simpa [normalEntries, hn, List.append_assoc] using hi.normal
  · simpa [heldEntries, hn] using hi.held

theorem GroPending.held_ready {g h e} (hi : GroPending g (some e) h)
    (hn : groTakenAtOnce e.bytes = false) (hempty : g.held = []) :
    GroReady {g with held := [e]} h := by
  refine ⟨hi.count, by simp, ?_, ?_⟩
  · simpa [normalEntries, hn] using hi.normal
  · simpa [heldEntries, hn, hempty] using hi.held

theorem groNormalOne_ready (g : TaggedGro) (e : GroEntry) (hn : groTakenAtOnce e.bytes = true) :
    PrefixEnsures (fun h _ => GroPending g (some e) h) SelectedGroSafe (groNormalOneTagged g e 1)
      (fun g' h _ => GroReady g' h) := by
  unfold groNormalOneTagged
  dsimp only
  split
  · apply (groNormalList_ready _).consequence
    · intro h w hi; exact hi.normal_ready hn
    · intro x h w hi; exact hi
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi.normal_ready hn)

theorem napiGroReceive_ready (g : TaggedGro) (e : GroEntry) :
    PrefixEnsures (fun h _ => GroPending g (some e) h) SelectedGroSafe (napiGroReceiveTagged g e)
      (fun g' h _ => GroReady g' h) := by
  unfold napiGroReceiveTagged
  split
  · exact groNormalOne_ready g e (by assumption)
  · rename_i hn
    have hn' : groTakenAtOnce e.bytes = false := by simpa using hn
    split
    · intro w h hi
      refine ⟨[], ?_, ?_, ?_⟩
      · change h = h ++ []; simp
      · change SelectedGroSafe h; exact hi.safe
      · change True; trivial
    · rename_i he
      have hempty : g.held = [] := by simpa using he
      exact PrefixEnsures.pure (fun _ _ hi => hi.safe)
        (fun _ _ hi => by simpa [hempty] using hi.held_ready hn' hempty)

theorem GroReady.rxList_normal {g h} (hi : GroReady g h) {e : GroEntry}
    (he : e ∈ g.rxList) : groTakenAtOnce e.bytes = true := by
  have hm : e ∈ normalEntries (bufferedEntries h) := by
    rw [hi.normal]
    exact List.mem_append_right _ he
  exact (List.mem_filter.mp hm).2

theorem GroReady.held_not_normal {g h} (hi : GroReady g h) {e : GroEntry}
    (he : e ∈ g.held) : groTakenAtOnce e.bytes = false := by
  have hm : e ∈ heldEntries (bufferedEntries h) := by rw [hi.held]; exact he
  have hp := (List.mem_filter.mp hm).2
  simpa using hp

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
  ⟨[], by simpa [GroComplete, selectedEntries, normalEntries, heldEntries] using hi⟩

theorem napiGroFlushAll_complete (g : TaggedGro) :
    PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe (napiGroFlushAllTagged g)
      (fun _ h _ => GroComplete h) := by
  intro w h hi
  rw [napiGroFlushAllTagged_eq g hi.count hi.heldSmall]
  have hf : PrefixEnsures (fun h _ => GroReady g h) SelectedGroSafe
      (flushGro (g.rxList ++ g.held)) (fun _ h _ => GroComplete h) := by
    apply (flushGro_selected (g.rxList ++ g.held) []).consequence
    · intro h _ hi
      change normalEntries _ ++ heldEntries _ = _
      rw [hi.normal, hi.held]
      simp only [List.append_assoc, List.append_nil]
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

theorem ready_lift_bind (a : M α) (g : TaggedGro) (f : α → PrefixM GroEvent β)
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
  change normalEntries _ ++ heldEntries _ = _
  rw [hi.normal, hi.held]
  simp

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
  exact ⟨rfl, by simp, rfl, rfl⟩

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
