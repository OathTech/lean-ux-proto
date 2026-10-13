import Leanux.Proofs.WG.Queues.RxPollGro
import Leanux.Proofs.WG.Queues.RxPollOrder

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

/-! Callback entries are exactly a visited prefix of the outer poll's tagged
GRO buffer. Completion returning none contributes no buffer occurrence;
stopping before the callback retains the outstanding buffer observations. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

def bufferedEntries (h : List GroEvent) : List GroEntry :=
  h.filterMap fun e => match e with | .buffered x => some x | _ => none

def enteredEntries (h : List GroEvent) : List GroEntry :=
  h.filterMap fun e => match e with | .entered x => some x | _ => none

def GroSafe (h : List GroEvent) : Prop :=
  ∃ remaining, bufferedEntries h = enteredEntries h ++ remaining

def GroInv (gro : List GroEntry) (h : List GroEvent) (_ : World) : Prop :=
  bufferedEntries h = gro ∧ enteredEntries h = []

theorem GroInv.safe {gro h w} (hi : GroInv gro h w) : GroSafe h := by
  exact ⟨gro, by simp [hi.1, hi.2]⟩

theorem gro_lift_bind (a : M α) (gro : List GroEntry) (f : α → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (GroInv gro) GroSafe (f x) Q) :
    PrefixEnsures (GroInv gro) GroSafe (liftPrefix a >>= f) Q :=
  PrefixEnsures.bind (PrefixEnsures.lift a (fun _ _ hi => hi.safe)
    (fun _ _ _ _ hi _ => hi)) hf

theorem dropGroPrefix_spec (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (gro : List GroEntry) :
    PrefixEnsures (GroInv gro) GroSafe (dropGroPrefix pid occurrence id) (fun _ => GroInv gro) := by
  intro w h hi
  simp only [dropGroPrefix, runPrefix_bind, runPrefix_lift]
  cases (dropRxQueue pid).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨u, v⟩
    cases u
    refine ⟨[.removed occurrence id], rfl, ?_, ?_⟩
    · simpa [GroSafe, bufferedEntries, enteredEntries, List.filterMap_append] using hi.safe
    · simpa [GroInv, bufferedEntries, enteredEntries, List.filterMap_append] using hi

theorem gro_drop_bind (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (gro : List GroEntry) (f : Unit → PrefixM GroEvent β)
    (hf : ∀ x, PrefixEnsures (GroInv gro) GroSafe (f x) Q) :
    PrefixEnsures (GroInv gro) GroSafe (dropGroPrefix pid occurrence id >>= f) Q :=
  PrefixEnsures.bind (dropGroPrefix_spec pid occurrence id gro) hf

/-- Only an actual successful completion returning bytes creates a buffered
occurrence. The original call's exact bytes and this call's ordinal/ID are kept. -/
theorem consumeGro_run (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) (w : World) (h : List GroEvent) :
    runPrefix (consumeGro pid occurrence id pkt endpoint) w h =
      match (consumeDataDone pid pkt endpoint).run w with
      | .error stop => (.error stop, h)
      | .ok (none, v) => (.ok (none, v), h)
      | .ok (some bytes, v) =>
        (.ok (some ⟨occurrence, id, bytes⟩, v), h ++ [.buffered ⟨occurrence, id, bytes⟩]) := by
  simp only [consumeGro, runPrefix_bind, runPrefix_lift]
  cases (consumeDataDone pid pkt endpoint).run w with
  | error e => rfl
  | ok out => rcases out with ⟨bytes, v⟩; cases bytes <;> rfl

theorem consumeGro_spec (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) (gro : List GroEntry) :
    PrefixEnsures (GroInv gro) GroSafe (consumeGro pid occurrence id pkt endpoint)
      (fun out => GroInv (gro ++ out.toList)) := by
  intro w h hi
  rw [consumeGro_run]
  cases hr : (consumeDataDone pid pkt endpoint).run w with
  | error e => exact ⟨[], by simp, hi.safe, True.intro⟩
  | ok out =>
    rcases out with ⟨bytes, v⟩
    cases bytes with
    | none => exact ⟨[], by simp, hi.safe, by simpa [GroInv] using hi⟩
    | some bytes =>
      refine ⟨[.buffered ⟨occurrence, id, bytes⟩], rfl, ?_, ?_⟩
      · have hb := hi.1
        have he := hi.2
        simp only [bufferedEntries, enteredEntries] at hb he
        exact ⟨gro ++ [⟨occurrence, id, bytes⟩], by
          simp [bufferedEntries, enteredEntries, List.filterMap_append, hb, he]⟩
      · simpa [GroInv, bufferedEntries, enteredEntries, List.filterMap_append] using
          (show bufferedEntries h = gro ∧ enteredEntries h = [] from hi)

theorem gro_consume_bind (pid : PeerId) (occurrence : Nat) (id : SkbId)
    (pkt : RxPacket) (endpoint : Endpoint) (gro : List GroEntry)
    (f : Option GroEntry → PrefixM GroEvent β)
    (hf : ∀ out, PrefixEnsures (GroInv (gro ++ out.toList)) GroSafe (f out) Q) :
    PrefixEnsures (GroInv gro) GroSafe (consumeGro pid occurrence id pkt endpoint >>= f) Q :=
  PrefixEnsures.bind (consumeGro_spec pid occurrence id pkt endpoint gro) hf

theorem flushGro_spec (gro : List GroEntry) :
    PrefixEnsures (GroInv gro) GroSafe (flushGro gro) (fun _ h _ => GroSafe h) := by
  intro w h hi
  obtain ⟨visited, remaining, he, hh, _⟩ := flushGro_prefix gro w h
  have hs : GroSafe (runPrefix (flushGro gro) w h).2 := by
    refine ⟨remaining, ?_⟩
    rw [hh]
    have hb := hi.1
    have hi' := hi.2
    simp only [bufferedEntries, enteredEntries] at hb hi'
    have hn : visited.filterMap (fun _ => (none : Option GroEntry)) = [] := by
      induction visited <;> simp_all
    simpa [bufferedEntries, enteredEntries, List.filterMap_append, List.filterMap_map, Function.comp_def, hb, hi', hn] using he
  refine ⟨visited.map GroEvent.entered, hh, hs, ?_⟩
  cases (runPrefix (flushGro gro) w h).1 <;> trivial

theorem gro_flush_bind (gro : List GroEntry) (f : Unit → PrefixM GroEvent α)
    (hf : ∀ x, PrefixEnsures (fun h _ => GroSafe h) GroSafe (f x) Q) :
    PrefixEnsures (GroInv gro) GroSafe (flushGro gro >>= f) Q :=
  PrefixEnsures.bind (flushGro_spec gro) hf

/-- For the complete original poll and its actual stack callback, the entered
occurrences are a prefix of the exact successful completion buffers. Errors
retain both the visited prefix and every buffered but unvisited occurrence. -/
theorem rxPollGro_spec (pid : PeerId) (budget : Nat) :
    PrefixEnsures (GroInv []) GroSafe (rxPollGro pid budget) (fun _ h _ => GroSafe h) := by
  unfold rxPollGro
  apply gro_lift_bind
  intro noBudget
  split
  · exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi.safe)
  · apply PrefixEnsures.bind (Q := fun acc => GroInv acc.2.1)
    · rw [Std.Legacy.Range.forIn_eq_forIn_range']
      apply PrefixEnsures.forInInvariant _ (0, [], false) _ (fun acc : Nat × List GroEntry × Bool => GroInv acc.2.1) GroSafe
        (fun _ _ _ hi => hi.safe)
      intro n acc
      repeat' first
        | with_reducible apply gro_lift_bind
        | with_reducible apply gro_drop_bind
        | with_reducible apply gro_consume_bind
        | with_reducible apply PrefixEnsures.ite
        | with_reducible exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi)
        | (with_reducible intro x; try dsimp only [ForInStep.value])
        | (with_reducible split)
    · intro acc
      repeat' first
        | with_reducible apply gro_lift_bind
        | with_reducible apply gro_flush_bind
        | with_reducible apply PrefixEnsures.ite
        | with_reducible exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi.safe)
        | with_reducible exact PrefixEnsures.pure (fun _ _ hi => hi) (fun _ _ hi => hi)
        | (with_reducible intro x; try dsimp only)
        | (with_reducible split)

theorem rxPollGro_callback_prefix (pid : PeerId) (budget : Nat) (w : World) :
    GroSafe (runPrefix (rxPollGro pid budget) w []).2 := by
  have hi : GroInv [] [] w := ⟨rfl, rfl⟩
  exact (rxPollGro_spec pid budget w [] hi).choose_spec.2.1

end Leanux.Proofs.WG.Queues
