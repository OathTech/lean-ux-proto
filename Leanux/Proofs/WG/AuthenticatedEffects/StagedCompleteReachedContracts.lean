import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCuts

/-! Result-sensitive composition preserves the same reached failure cut.
Unlike a history-only safety predicate, each stopped branch is indexed by the
original caller, its input world and journal, and its actual Stop result. This
is a local proof interface; no initialized driver instance is asserted here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.Proofs.Logged

theorem Failure.bind_left {body : PrefixM CausalJournal.Event α}
    (failure : Failure context body w history reason last)
    (next : α → PrefixM CausalJournal.Event β) :
    Nonempty (Failure context (body >>= next) w history reason last) :=
  ⟨⟨failure.cut,failure.valid,.left failure.reached⟩⟩

theorem Failure.bind_right {body : PrefixM CausalJournal.Event α}
    {next : α → PrefixM CausalJournal.Event β}
    (prefixRun : runPrefix body w history = (.ok (value,v),after))
    (failure : Failure context (next value) v after reason last) :
    Nonempty (Failure context (body >>= next) w history reason last) :=
  ⟨⟨failure.cut,failure.valid,.right prefixRun failure.reached⟩⟩

def Stopped (body : PrefixM CausalJournal.Event α) (w : World)
    (history : List CausalJournal.Event) (reason : Stop) (last : List CausalJournal.Event) : Prop :=
  ∃ context, Nonempty (Failure context body w history reason last)

def Ensures (P : List CausalJournal.Event → World → Prop)
    (body : PrefixM CausalJournal.Event α)
    (Q : α → List CausalJournal.Event → World → Prop) : Prop :=
  ∀ w history, P history w →
    match runPrefix body w history with
    | (.error reason,last) => Stopped body w history reason last
    | (.ok (value,v),last) => Q value last v

theorem Ensures.pure (value : α) : Ensures P (pure value)
    (fun out history w => out = value ∧ P history w) := by
  intro w history before
  exact ⟨rfl,before⟩

/-- A stopped left or right source retains its own accounted native cut;
the right case additionally retains the exact successful left run. -/
theorem Ensures.bind {body : PrefixM CausalJournal.Event α}
    {next : α → PrefixM CausalJournal.Event β}
    (head : Ensures P body Q) (tail : ∀ value, Ensures (Q value) (next value) R) :
    Ensures P (body >>= next) R := by
  intro w history before
  have first := head w history before
  rw [runPrefix_bind]
  cases prefixRun : runPrefix body w history with
  | mk result after =>
    rw [prefixRun] at first
    cases result with
    | error reason =>
      dsimp only at first ⊢
      obtain ⟨context,⟨failure⟩⟩ := first
      exact ⟨context,failure.bind_left next⟩
    | ok out =>
      obtain ⟨value,v⟩ := out
      dsimp only at first ⊢
      have second := tail value v after first
      cases suffixRun : runPrefix (next value) v after with
      | mk result last =>
        rw [suffixRun] at second
        cases result with
        | error reason =>
          obtain ⟨context,⟨failure⟩⟩ := second
          exact ⟨context,Failure.bind_right prefixRun failure⟩
        | ok out => exact second

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
