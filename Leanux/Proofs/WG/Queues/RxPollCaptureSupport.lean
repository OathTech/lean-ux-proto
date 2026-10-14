import Leanux.Proofs.WG.Queues.RxPollStampPhase

/-! The original capture read supports each stamped removal in the new poll
suffix. The journal proof is independent of allocation safety; the latter then
excludes earlier releases. No additional getter or capture event is introduced. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

def readEvent (skb : SkbId) (stamp : PacketStamp) : Event :=
  .access (.packet (.read (.inr skb) stamp))

def ReadSince (base h : List Event) (skb : SkbId) (stamp : PacketStamp) : Prop :=
  ∃ before after, h = base ++ before ++ [readEvent skb stamp] ++ after

def ReadBeforeRemoval (base h : List Event) (k : EntryKey) : Prop :=
  ∃ before middle after, h = base ++ before ++ [readEvent k.2.1 k.2.2] ++
    middle ++ [.removed k.1 k.2.1 k.2.2] ++ after

structure ReadSupport (base h : List Event) : Prop where
  extension : ∃ suffix, h = base ++ suffix
  removed : ∀ k ∈ removalKeys h, ReadBeforeRemoval base h k

def ReadContext (base : List Event) (pending : Option (SkbId × PacketStamp))
    (h : List Event) : Prop := ReadSupport base h ∧
  ∀ p ∈ pending, ReadSince base h p.1 p.2

theorem ReadSince.append (hi : ReadSince base h skb stamp) (tail : List Event) :
    ReadSince base (h ++ tail) skb stamp := by
  obtain ⟨a, b, rfl⟩ := hi
  exact ⟨a, b ++ tail, by simp only [List.append_assoc]⟩

theorem ReadBeforeRemoval.append (hi : ReadBeforeRemoval base h k) (tail : List Event) :
    ReadBeforeRemoval base (h ++ tail) k := by
  obtain ⟨a, b, c, rfl⟩ := hi
  exact ⟨a, b, c ++ tail, by simp only [List.append_assoc]⟩

theorem removalKeys_frame (ha : Appends a) (hm : HistoryFrame removedStamp a) :
    HistoryFrame removedKey a := by
  intro w h
  obtain ⟨tail, ht⟩ := ha w h
  have hs : removedStamps tail = [] := by
    have he := hm w h
    change removedStamps (runPrefix a w h).2 = removedStamps h at he
    rw [ht, removedStamps, List.filterMap_append] at he
    exact List.append_cancel_left (he.trans (List.append_nil _).symm)
  have hk : removalKeys tail = [] := by
    have he := removalKeys_stamps tail
    rw [hs] at he
    cases hh : removalKeys tail with
    | nil => rfl
    | cons x xs => simp [hh] at he
  change removalKeys (runPrefix a w h).2 = removalKeys h
  rw [ht]
  change (h ++ tail).filterMap removedKey = h.filterMap removedKey
  rw [List.filterMap_append]
  change removalKeys h ++ removalKeys tail = removalKeys h
  rw [hk, List.append_nil]

theorem read_quiet (base : List Event) (pending : Option (SkbId × PacketStamp))
    (a : Obs α) (ha : Appends a) (hm : HistoryFrame removedStamp a) :
    PrefixPreserves (fun h _ => ReadContext base pending h) (ReadSupport base) a := by
  intro w h hi
  obtain ⟨tail, ht⟩ := ha w h
  have hk : removalKeys (h ++ tail) = removalKeys h := by
    simpa only [ht, removalKeys] using removalKeys_frame ha hm w h
  have hc : ReadContext base pending (h ++ tail) := by
    refine ⟨⟨?_, fun k hk' => (hi.1.removed k (hk ▸ hk')).append tail⟩, ?_⟩
    · obtain ⟨old, rfl⟩ := hi.1.extension
      exact ⟨old ++ tail, by simp only [List.append_assoc]⟩
    · exact fun p hp => (hi.2 p hp).append tail
  refine ⟨tail, ht, ht ▸ hc.1, ?_⟩
  cases (runPrefix a w h).1
  · trivial
  · exact ht ▸ hc

theorem read_access (base : List Event) (pending : Option (SkbId × PacketStamp))
    (a : MixedM α) :
    PrefixPreserves (fun h _ => ReadContext base pending h) (ReadSupport base) (access a) :=
  read_quiet base pending _ (access_appends a)
    (fun w h => focusPrefix_other Event.access accessEvent removedStamp (fun _ => rfl) a w h)

theorem read_lift (base : List Event) (pending : Option (SkbId × PacketStamp)) (a : M α) :
    PrefixPreserves (fun h _ => ReadContext base pending h) (ReadSupport base) (liftPrefix a) :=
  read_quiet base pending _ (Appends.lift a) (HistoryFrame.lift _ a)

theorem read_capture (base : List Event) (skb : SkbId) :
    PrefixEnsures (fun h _ => ReadContext base none h) (ReadSupport base) (capture skb)
      (fun out h _ => ReadContext base (some (skb, out.2)) h) := by
  intro w h hi
  rw [capture_run]
  cases hg : (getRxSkb skb).run w with
  | error e => exact ⟨[], by simp, hi.1, True.intro⟩
  | ok out =>
    have hm : HistoryFrame removedStamp (capture skb) := by
      intro w h; rw [capture_run]
      cases (getRxSkb skb).run w <;> simp [removedStamp, List.filterMap_append]
    have hs := (read_quiet base none _ (capture_appends skb) hm w h hi).choose_spec.2.1
    rw [capture_run, hg] at hs
    refine ⟨[readEvent skb (packetStamp w skb)], rfl, hs, hs, ?_⟩
    intro p hp
    simp only [Option.mem_some_iff] at hp
    subst p
    obtain ⟨old, he⟩ := hi.1.extension
    exact ⟨old, [], by simp only [he, List.append_nil, readEvent]⟩

theorem read_mark (base : List Event) (n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (fun h _ => ReadContext base (some (skb, stamp)) h) (ReadSupport base)
      (emitPrefix (.removed n skb stamp)) (fun _ h _ => ReadContext base none h) := by
  intro w h hi
  have hs : ReadSupport base (h ++ [.removed n skb stamp]) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨old, rfl⟩ := hi.1.extension
      exact ⟨old ++ [.removed n skb stamp], by simp only [List.append_assoc]⟩
    · intro k hk
      simp only [removalKeys, List.filterMap_append, List.filterMap_cons, removedKey,
        List.filterMap_nil, List.mem_append, List.mem_singleton] at hk
      rcases hk with old | rfl
      · exact (hi.1.removed k old).append _
      · obtain ⟨a, b, he⟩ := hi.2 (skb, stamp) (by simp)
        exact ⟨a, b, [], by simp only [he, List.append_nil, readEvent]⟩
  exact ⟨[.removed n skb stamp], rfl, hs, hs, by simp⟩

theorem read_drop (base : List Event) (pid n skb : Nat) (stamp : PacketStamp) :
    PrefixEnsures (fun h _ => ReadContext base (some (skb, stamp)) h) (ReadSupport base)
      (drop pid n skb stamp) (fun _ h _ => ReadContext base none h) := by
  unfold drop
  exact PrefixEnsures.bind (Q := fun _ h _ => ReadContext base (some (skb, stamp)) h)
    (read_access base _ _) (fun _ => read_mark base n skb stamp)

theorem read_bind (base : List Event) (pending : Option (SkbId × PacketStamp))
    (a : Obs α) (f : α → Obs β)
    (ha : PrefixPreserves (fun h _ => ReadContext base pending h) (ReadSupport base) a)
    (hf : ∀ x, PrefixEnsures (fun h _ => ReadContext base pending h) (ReadSupport base) (f x) Q) :
    PrefixEnsures (fun h _ => ReadContext base pending h) (ReadSupport base) (a >>= f) Q :=
  PrefixEnsures.bind (Q := fun _ h _ => ReadContext base pending h) ha hf

theorem read_option (base : List Event) (pending : Option (SkbId × PacketStamp))
    (out : Option Entry) (g : Gro) :
    PrefixPreserves (fun h _ => ReadContext base pending h) (ReadSupport base)
      (forIn out.toList g (fun e g => do let g' ← receive g e; pure (.yield g'))) :=
  PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1)
    (fun e g => PrefixPreserves.bind
      (read_quiet base pending _ (receive_appends g e) (receive_removed g e))
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.1) _))

theorem read_stop (base : List Event) (pending : Option (SkbId × PacketStamp))
    (a : M Unit) (ha : ∀ w, ∃ e, a.run w = .error e) (f : Unit → Obs α) :
    PrefixEnsures (fun h _ => ReadContext base pending h) (ReadSupport base)
      (liftPrefix a >>= f) Q := by
  intro w h hi
  obtain ⟨e, he⟩ := ha w
  simp only [runPrefix_bind, runPrefix_lift, he]
  exact ⟨[], by simp, hi.1, True.intro⟩

macro "rx_read_step" : tactic => `(tactic|
  repeat' first
    | exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
    | with_reducible apply read_stop _ _ (invariant _) (fun _ => ⟨_, rfl⟩)
    | with_reducible apply read_stop _ _ (unsupported _) (fun _ => ⟨_, rfl⟩)
    | with_reducible apply PrefixEnsures.bind (read_capture _ _)
    | with_reducible apply PrefixEnsures.bind (read_drop _ _ _ _ _)
    | with_reducible apply read_bind _ _ _ _ (read_quiet _ _ _ (consume_appends _ _ _ _ _ _) (consume_removed _ _ _ _ _ _))
    | with_reducible apply read_bind _ _ _ _ (read_quiet _ _ _ (receive_appends _ _) (receive_removed _ _))
    | with_reducible apply read_bind _ _ _ _ (read_quiet _ _ _ (flushAll_appends _) (flushAll_removed _))
    | with_reducible apply read_bind _ _ _ _ (read_option _ _ _ _)
    | with_reducible apply read_bind _ _ _ _ (read_access _ _ _)
    | with_reducible apply read_bind _ _ _ _ (read_lift _ _ _)
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.1)
    | with_reducible apply PrefixEnsures.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split))

theorem poll_read_support (base : List Event) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _ => ReadContext base none h) (ReadSupport base) (poll pid budget) := by
  change PrefixEnsures (fun h _ => ReadContext base none h) (ReadSupport base) _ (fun _ h _ => ReadContext base none h)
  unfold poll
  apply read_bind base none _ _ (read_lift _ _ _)
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => hi)
  · apply PrefixEnsures.bind (Q := fun _ h _ => ReadContext base none h)
    · change PrefixPreserves (fun h _ => ReadContext base none h) (ReadSupport base) _
      apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.1)
      intro index acc
      change PrefixEnsures (fun h _ => ReadContext base none h) (ReadSupport base) _ (fun _ h _ => ReadContext base none h)
      rx_read_step
    · intro acc
      rx_read_step

theorem seed_read_context (prior : List LifetimeEvent) :
    ReadContext (seed prior) none (seed prior) := by
  refine ⟨⟨⟨[], by simp⟩, ?_⟩, by simp⟩
  intro k hk
  have he : removalKeys (seed prior) = [] :=
    filterMap_disjoint Event.access removedKey (fun _ => rfl) prior
  rw [he] at hk
  contradiction

/-- Every removal has its matching original capture read before it, within
this poll's new suffix. This source-support statement needs no state invariant. -/
theorem poll_capture_support (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) :
    ReadSupport (seed prior) (runPrefix (poll pid budget) w (seed prior)).2 :=
  (poll_read_support (seed prior) pid budget w (seed prior) (seed_read_context prior)).choose_spec.2.1


@[simp] theorem seed_removals (prior : List LifetimeEvent) : removalKeys (seed prior) = [] :=
  filterMap_disjoint Event.access removedKey (fun _ => rfl) prior

@[simp] theorem seed_entries (prior : List LifetimeEvent) : entries (seed prior) = [] :=
  filterMap_disjoint Event.access enteredEntry (fun _ => rfl) prior

@[simp] theorem seed_removed_stamps (prior : List LifetimeEvent) : removedStamps (seed prior) = [] :=
  filterMap_disjoint Event.access removedStamp (fun _ => rfl) prior

/-- Ordered support lies in the appended suffix, never merely in prior history. -/
theorem poll_suffix_read_before (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (suffix : List Event)
    (he : (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix)
    (k : EntryKey) (hk : k ∈ removalKeys suffix) :
    ReadBeforeRemoval [] suffix k := by
  have hs := poll_capture_support pid budget w prior
  have hm : k ∈ removalKeys (runPrefix (poll pid budget) w (seed prior)).2 := by
    rw [he]
    simp only [removalKeys, List.filterMap_append, List.mem_append]
    exact Or.inr hk
  obtain ⟨a, b, c, hr⟩ := hs.removed k hm
  refine ⟨a, b, c, ?_⟩
  rw [he] at hr
  simpa only [List.nil_append] using
    List.append_cancel_left (by simpa only [List.append_assoc] using hr)

/-- An entered payload's complete key has the same suffix-local capture/read
support as its removal. This does not assert callback completion. -/
theorem poll_suffix_entry_read_before (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (suffix : List Event)
    (he : (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix)
    (e : Entry) (hm : e ∈ entries suffix) : ReadBeforeRemoval [] suffix e.key := by
  have support := poll_entry_support pid budget w prior
  have hentry : e ∈ entries (runPrefix (poll pid budget) w (seed prior)).2 := by
    simp only [he, entries, List.filterMap_append, List.mem_append]
    exact Or.inr hm
  have hk := support e hentry
  have keys : removalKeys (runPrefix (poll pid budget) w (seed prior)).2 = removalKeys suffix := by
    simp only [he, removalKeys, List.filterMap_append]
    change removalKeys (seed prior) ++ removalKeys suffix = removalKeys suffix
    rw [seed_removals, List.nil_append]
  rw [keys] at hk
  exact poll_suffix_read_before pid budget w prior suffix he e.key hk

theorem ReadBeforeRemoval.read_mem (hr : ReadBeforeRemoval [] suffix k) :
    readEvent k.2.1 k.2.2 ∈ suffix := by
  obtain ⟨a, b, c, rfl⟩ := hr
  simp

def PriorReleased (prior : List LifetimeEvent) (stamp : PacketStamp) : Prop :=
  AccessEvent.Released (prior.filterMap LifetimeEvent.packet?) stamp

theorem safe_suffix_read_fresh (prior : List LifetimeEvent) (suffix : List Event)
    (hs : LifetimeEvent.Safe (prior ++ suffix.filterMap accessEvent))
    (skb : SkbId) (stamp : PacketStamp) (hr : readEvent skb stamp ∈ suffix) :
    ¬ PriorReleased prior stamp := by
  intro released
  obtain ⟨slot, hm⟩ := released
  have hh := hs.2.2
  rw [List.filterMap_append] at hh
  have readMem : AccessEvent.read (.inr skb) stamp ∈
      (suffix.filterMap accessEvent).filterMap LifetimeEvent.packet? := by
    apply List.mem_filterMap.mpr
    refine ⟨.packet (.read (.inr skb) stamp), ?_, rfl⟩
    exact List.mem_filterMap.mpr ⟨readEvent skb stamp, hr, rfl⟩
  exact (List.pairwise_append.mp hh).2.2 _ hm _ readMem rfl

/-- Prior releases exclude every newly removed and callback-entered stamp,
including prefixes stopped inside the callback. No normal-return premise is used. -/
theorem poll_suffix_fresh (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (hi : AllocationInv prior w) (suffix : List Event)
    (he : (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix) :
    (∀ k ∈ removalKeys suffix, ¬ PriorReleased prior k.2.2) ∧
      (∀ e ∈ entries suffix, ¬ PriorReleased prior e.stamp) := by
  obtain ⟨s, hs, safe, _⟩ := poll_safe_suffix pid budget w prior hi
  have same : s = suffix := List.append_cancel_left (hs.symm.trans he)
  subst s
  have fresh : ∀ k ∈ removalKeys suffix, ¬ PriorReleased prior k.2.2 :=
    fun k hk => safe_suffix_read_fresh prior suffix safe _ _
      (poll_suffix_read_before pid budget w prior suffix he k hk).read_mem
  refine ⟨fresh, ?_⟩
  intro e hm
  have support := poll_entry_support pid budget w prior
  have hentry : e ∈ entries (runPrefix (poll pid budget) w (seed prior)).2 := by
    simp only [he, entries, List.filterMap_append, List.mem_append]
    exact Or.inr hm
  have hk := support e hentry
  have keys : removalKeys (runPrefix (poll pid budget) w (seed prior)).2 = removalKeys suffix := by
    simp only [he, removalKeys, List.filterMap_append]
    change removalKeys (seed prior) ++ removalKeys suffix = removalKeys suffix
    rw [seed_removals, List.nil_append]
  rw [keys] at hk
  exact fresh e.key hk

/-- Local suffix entries are distinct. On normal return their actual releases
also lie in this suffix; they cannot be borrowed from the incoming history. -/
theorem poll_suffix_entries (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (hi : AllocationInv prior w) (suffix : List Event)
    (he : (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix) :
    ((entries suffix).map Entry.stamp).Nodup ∧
      (match (runPrefix (poll pid budget) w (seed prior)).1 with
       | .error _ => True
       | .ok _ => ∀ e ∈ entries suffix, Released suffix e.stamp) := by
  have hp := poll_entry_stamps pid budget w prior hi
  have hentries : entries (runPrefix (poll pid budget) w (seed prior)).2 = entries suffix := by
    simp only [he, entries, List.filterMap_append]
    change entries (seed prior) ++ entries suffix = entries suffix
    rw [seed_entries, List.nil_append]
  dsimp only at hp
  rw [hentries] at hp
  refine ⟨hp.1, ?_⟩
  cases hr : (runPrefix (poll pid budget) w (seed prior)).1 with
  | error e => trivial
  | ok out =>
    have rel := hp.2
    simp only [hr] at rel
    intro e hm
    have hh := rel e hm
    rw [he] at hh
    have split : PriorReleased prior e.stamp ∨ Released suffix e.stamp := by
      simpa only [Released, List.filterMap_append, seed_access, AccessEvent.released_append,
        PriorReleased] using hh
    exact split.resolve_left ((poll_suffix_fresh pid budget w prior hi suffix he).2 e hm)

/-- Normal return releases every removal in the new suffix, including explicit
drops which never produce a GRO payload. -/
theorem poll_suffix_removal_release (pid : PeerId) (budget : Nat) (w : World)
    (prior : List LifetimeEvent) (hi : AllocationInv prior w) (suffix : List Event)
    (he : (runPrefix (poll pid budget) w (seed prior)).2 = seed prior ++ suffix) :
    match (runPrefix (poll pid budget) w (seed prior)).1 with
    | .error _ => True
    | .ok _ => ∀ k ∈ removalKeys suffix, Released suffix k.2.2 := by
  have hp := (poll_removed_stamps pid budget w prior hi).2
  cases hr : (runPrefix (poll pid budget) w (seed prior)).1 with
  | error e => trivial
  | ok out =>
    simp only [hr] at hp
    intro k hk
    have hm : k.2.2 ∈ removedStamps suffix := by
      rw [← removalKeys_stamps]
      exact List.mem_map.mpr ⟨k, hk, rfl⟩
    have hall : k.2.2 ∈ removedStamps (runPrefix (poll pid budget) w (seed prior)).2 := by
      rw [he]
      simp only [removedStamps, List.filterMap_append, List.mem_append]
      exact Or.inr hm
    have hh := hp k.2.2 hall
    rw [he] at hh
    have split : PriorReleased prior k.2.2 ∨ Released suffix k.2.2 := by
      simpa only [Released, List.filterMap_append, seed_access, AccessEvent.released_append,
        PriorReleased] using hh
    exact split.resolve_left ((poll_suffix_fresh pid budget w prior hi suffix he).1 k hk)

end Leanux.Proofs.WG.Queues.RxJoint
