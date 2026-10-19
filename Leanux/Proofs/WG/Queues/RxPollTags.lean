import Leanux.Proofs.WG.Queues.SelectedGro

/-! Local occurrence provenance within the unchanged poll observer. Ordinals
count successful outer queue drops; they are not allocation identities. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

def removedTags (h : List GroEvent) : List (Nat × SkbId) :=
  h.filterMap fun e => match e with
    | .removed n id => some (n, id)
    | _ => none

def bufferedTags (h : List GroEvent) : List (Nat × SkbId) :=
  (bufferedEntries h).map fun e => (e.occurrence, e.skb)

structure TagReady (n : Nat) (h : List GroEvent) : Prop where
  ordinals : (removedTags h).map Prod.fst = List.range n
  buffered : (bufferedTags h).Sublist (removedTags h)

def TagSafe (h : List GroEvent) : Prop := ∃ n, TagReady n h

def TagDropped (n id : Nat) (h : List GroEvent) : Prop :=
  ∃ before : List (Nat × SkbId), removedTags h = before ++ [(n, id)] ∧
    before.map Prod.fst = List.range n ∧ (bufferedTags h).Sublist before

theorem TagReady.safe {n h} (hi : TagReady n h) : TagSafe h := ⟨n, hi⟩

theorem TagDropped.next {n id h} (hi : TagDropped n id h) : TagReady (n + 1) h := by
  rcases hi with ⟨before, hr, ho, hb⟩
  refine ⟨?_, ?_⟩
  · rw [hr, List.map_append, ho, List.range_succ]
    rfl
  · rw [hr]
    exact List.sublist_append_of_sublist_left hb

theorem TagDropped.safe {n id h} (hi : TagDropped n id h) : TagSafe h := hi.next.safe

@[simp] theorem removed_append_entered (h : List GroEvent) (xs : List GroEntry) :
    removedTags (h ++ xs.map GroEvent.entered) = removedTags h := by
  have hn : xs.filterMap (fun _ => (none : Option (Nat × SkbId))) = [] := by
    induction xs <;> simp_all
  simp [removedTags, List.filterMap_append, List.filterMap_map, Function.comp_def, hn]

@[simp] theorem bufferedTags_append_entered (h : List GroEvent) (xs : List GroEntry) :
    bufferedTags (h ++ xs.map GroEvent.entered) = bufferedTags h := by
  simp only [bufferedTags, buffered_append_entered]

theorem TagReady.entered {n h} (hi : TagReady n h) (xs : List GroEntry) :
    TagReady n (h ++ xs.map GroEvent.entered) := by
  exact ⟨by simpa using hi.ordinals, by simpa using hi.buffered⟩

theorem tag_lift (a : Leanux.M α) (I : List GroEvent → Prop) (hs : ∀ h, I h → TagSafe h) :
    PrefixEnsures (fun h _ => I h) TagSafe (liftPrefix a) (fun _ h _ => I h) :=
  PrefixEnsures.lift a (fun h _ => hs h) (fun _ _ _ _ hi _ => hi)

theorem tag_lift_bind (a : Leanux.M α) (I : List GroEvent → Prop) (hs : ∀ h, I h → TagSafe h)
    (f : α → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => I h) TagSafe (f x) Q) :
    PrefixEnsures (fun h _ => I h) TagSafe (liftPrefix a >>= f) Q :=
  PrefixEnsures.bind (tag_lift a I hs) hf

theorem dropGro_tags (pid n id : Nat) :
    PrefixEnsures (fun h _ => TagReady n h) TagSafe (dropGroPrefix pid n id)
      (fun _ h _ => TagDropped n id h) := by
  intro w h hi
  simp only [dropGroPrefix, runPrefix_bind, runPrefix_lift]
  cases (liftWG (dropRxQueue pid)).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨u, v⟩
    cases u
    have hh : TagDropped n id (h ++ [.removed n id]) := by
      refine ⟨removedTags h, ?_, hi.ordinals, ?_⟩
      · simp [removedTags, List.filterMap_append]
      · simpa [bufferedTags, bufferedEntries, List.filterMap_append] using hi.buffered
    exact ⟨[.removed n id], rfl, hh.safe, hh⟩

theorem TagDropped.buffered_entry {n id h} (hi : TagDropped n id h) (bytes : List UInt8) :
    TagReady (n + 1) (h ++ [.buffered ⟨n, id, bytes⟩]) := by
  refine ⟨?_, ?_⟩
  · simpa [removedTags, List.filterMap_append] using hi.next.ordinals
  · simp only [bufferedTags, bufferedEntries, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.map_append, List.map_cons, List.map_nil,
      removedTags, List.append_nil]
    change (bufferedTags h ++ [(n, id)]).Sublist (removedTags h)
    rcases hi with ⟨before, hr, ho, hb⟩
    rw [hr]
    exact hb.append_right _

theorem consumeGro_tags (pid n id : Nat) (pkt : RxPacket) (endpoint : Endpoint) :
    PrefixEnsures (fun h _ => TagDropped n id h) TagSafe (consumeGro pid n id pkt endpoint)
      (fun _ h _ => TagReady (n + 1) h) := by
  intro w h hi
  rw [consumeGro_run]
  cases (liftWG (consumeDataDone pid pkt endpoint)).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨bytes, v⟩
    cases bytes with
    | none => exact ⟨[], by simp, hi.safe, hi.next⟩
    | some bytes =>
      have hp := hi.buffered_entry bytes
      exact ⟨[.buffered ⟨n, id, bytes⟩], rfl, hp.safe, hp⟩

theorem flushGro_tags (xs : List GroEntry) (n : Nat) :
    PrefixPreserves (fun h _ => TagReady n h) TagSafe (flushGro xs) := by
  intro w h hi
  obtain ⟨visited, remaining, he, hh, hok⟩ := flushGro_prefix xs w h
  have ht : TagReady n (runPrefix (flushGro xs) w h).2 := by rw [hh]; exact hi.entered visited
  refine ⟨visited.map GroEvent.entered, hh, ht.safe, ?_⟩
  cases (runPrefix (flushGro xs) w h).1 <;> trivial

theorem groNormalList_tags (g : TaggedGro) (n : Nat) :
    PrefixPreserves (fun h _ => TagReady n h) TagSafe (groNormalListTagged g) := by
  unfold groNormalListTagged
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
  · exact PrefixPreserves.bind (flushGro_tags _ n)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _)

theorem groNormalOne_tags (g : TaggedGro) (e : GroEntry) (segs n : Nat) :
    PrefixPreserves (fun h _ => TagReady n h) TagSafe (groNormalOneTagged g e segs) := by
  unfold groNormalOneTagged
  dsimp only
  split
  · exact groNormalList_tags _ n
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _

theorem napiGroReceive_tags (g : TaggedGro) (e : GroEntry) (n : Nat) :
    PrefixPreserves (fun h _ => TagReady n h) TagSafe (napiGroReceiveTagged g e) := by
  unfold napiGroReceiveTagged
  repeat' first
    | exact groNormalOne_tags _ _ _ n
    | exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | exact (tag_lift _ (TagReady n) (fun _ hi => hi.safe)).preserves
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem napiGroFlushAll_tags (g : TaggedGro) (n : Nat) :
    PrefixPreserves (fun h _ => TagReady n h) TagSafe (napiGroFlushAllTagged g) := by
  unfold napiGroFlushAllTagged
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    intro e g
    exact PrefixPreserves.bind (groNormalOne_tags g e 1 n)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
  · intro g
    exact PrefixPreserves.bind (groNormalList_tags _ n)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _)

theorem tag_drop_bind (pid n id : Nat) (f : Unit → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => TagDropped n id h) TagSafe (f x) Q) :
    PrefixEnsures (fun h _ => TagReady n h) TagSafe (dropGroPrefix pid n id >>= f) Q :=
  PrefixEnsures.bind (dropGro_tags pid n id) hf

theorem tag_consume_bind (pid n id : Nat) (pkt : RxPacket) (endpoint : Endpoint)
    (f : Option GroEntry → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => TagReady (n + 1) h) TagSafe (f x) Q) :
    PrefixEnsures (fun h _ => TagDropped n id h) TagSafe (consumeGro pid n id pkt endpoint >>= f) Q :=
  PrefixEnsures.bind (consumeGro_tags pid n id pkt endpoint) hf

theorem tag_option_bind (n : Nat) (g : TaggedGro) (out : Option GroEntry)
    (f : TaggedGro → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => TagReady n h) TagSafe (f x) Q) :
    PrefixEnsures (fun h _ => TagReady n h) TagSafe
      ((forIn out.toList g (fun e g => do let g' ← napiGroReceiveTagged g e; pure (.yield g'))) >>= f) Q := by
  apply PrefixEnsures.bind (Q := fun _ h _ => TagReady n h) _ hf
  exact PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    (fun e g => PrefixPreserves.bind (napiGroReceive_tags g e n)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _))

theorem tag_flush_bind (n : Nat) (g : TaggedGro) (f : Unit → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (fun h _ => TagReady n h) TagSafe (f x) Q) :
    PrefixEnsures (fun h _ => TagReady n h) TagSafe (napiGroFlushAllTagged g >>= f) Q :=
  PrefixEnsures.bind (Q := fun _ h _ => TagReady n h) (napiGroFlushAll_tags g n) hf

theorem tag_invariant_bind (why : String) (f : Unit → PrefixM GroEvent α)
    (hs : ∀ h w, P h w → TagSafe h) :
    PrefixEnsures P TagSafe (liftPrefix (invariant why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hs h w hi, True.intro⟩

theorem tag_unsupported_bind (why : String) (f : Unit → PrefixM GroEvent α)
    (hs : ∀ h w, P h w → TagSafe h) :
    PrefixEnsures P TagSafe (liftPrefix (unsupported why) >>= f) Q := by
  intro w h hi
  exact ⟨[], by change h = h ++ []; simp, hs h w hi, True.intro⟩

theorem rxPollGro_tags_spec (pid : PeerId) (budget : Nat) :
    PrefixEnsures (fun h _ => TagReady 0 h) TagSafe (rxPollGro pid budget)
      (fun n h _ => TagReady n h) := by
  unfold rxPollGro
  apply tag_lift_bind _ _ (fun _ hi => hi.safe)
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := fun acc : Nat × TaggedGro × Bool => fun h _ => TagReady acc.1 h)
    · with_reducible apply (PrefixEnsures.rangeInvariant _ (0, ({} : TaggedGro), false) _
        (fun acc : Nat × TaggedGro × Bool => fun h _ => TagReady acc.1 h) TagSafe
        (fun _ _ _ hi => hi.safe))
      intro index acc
      repeat' first
        | exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
        | exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi.next)
        | with_reducible apply tag_invariant_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply tag_unsupported_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply tag_drop_bind
        | with_reducible apply tag_consume_bind
        | with_reducible apply tag_option_bind
        | with_reducible apply tag_lift_bind _ _ (fun _ hi => hi.safe)
        | with_reducible apply PrefixEnsures.ite
        | (with_reducible intro x; try dsimp only)
        | (with_reducible split)
    · intro acc
      repeat' first
        | exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
        | with_reducible apply tag_invariant_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply tag_unsupported_bind _ _ (fun _ _ hi => hi.safe)
        | with_reducible apply tag_flush_bind
        | with_reducible apply tag_lift_bind _ _ (fun _ hi => hi.safe)
        | with_reducible apply PrefixEnsures.ite
        | (with_reducible intro x; try dsimp only)
        | (with_reducible split)

theorem tagReady_initial : TagReady 0 [] := ⟨rfl, List.Sublist.refl _⟩

theorem rxPollGro_tags_safe (pid : PeerId) (budget : Nat) (w : World) :
    TagSafe (runPrefix (rxPollGro pid budget) w []).2 :=
  (rxPollGro_tags_spec pid budget w [] tagReady_initial).choose_spec.2.1

theorem TagSafe.properties {h} (hs : TagSafe h) :
    (bufferedTags h).Sublist (removedTags h) ∧
      (removedTags h).map Prod.fst = List.range (removedTags h).length ∧
      ((bufferedEntries h).map GroEntry.occurrence).Nodup := by
  obtain ⟨n, hi⟩ := hs
  have hn : (removedTags h).length = n := by
    simpa using congrArg List.length hi.ordinals
  refine ⟨hi.buffered, by simpa only [hn] using hi.ordinals, ?_⟩
  have hd : ((removedTags h).map Prod.fst).Nodup := by
    rw [hi.ordinals]
    exact List.nodup_range
  have hb := (hi.buffered.map Prod.fst).nodup hd
  simpa only [bufferedTags, List.map_map, Function.comp_def] using hb

theorem rxPollGro_tags_properties (pid : PeerId) (budget : Nat) (w : World) :
    let h := (runPrefix (rxPollGro pid budget) w []).2
    (bufferedTags h).Sublist (removedTags h) ∧
      (removedTags h).map Prod.fst = List.range (removedTags h).length ∧
      ((bufferedEntries h).map GroEntry.occurrence).Nodup :=
  (rxPollGro_tags_safe pid budget w).properties

end Leanux.Proofs.WG.Queues
