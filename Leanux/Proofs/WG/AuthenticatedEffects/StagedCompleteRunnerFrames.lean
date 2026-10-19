import Leanux.Proofs.WG.RetirementSecurity.TxWorkRunner

/-! The original runner's administrative tail appends no journal events.
Its real normal-exit guards supply both incoming and outgoing suspension
quiescence. These frames also retain the actual history on a stopped tail. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits RetirementSecurity

variable {E α β γ : Type}

def Quiet (action : PrefixOuter E α) : Prop :=
  ∀ h, (runPrefixOuter action h).2 = h

theorem Quiet.pure (value : α) : Quiet (E:=E) (pure value) := fun _ => rfl

theorem Quiet.stopped (reason : Nat × Stop) : Quiet (E:=E) (α:=α) (throw reason) := fun _ => rfl

theorem Quiet.bind {front : PrefixOuter E α} {tail : α → PrefixOuter E β}
    (before : Quiet front) (after : ∀ x, Quiet (tail x)) : Quiet (front >>= tail) := by
  intro h
  rw [runPrefixOuter_bind]
  have old := before h
  cases source : runPrefixOuter front h with
  | mk outcome k =>
    rw [source] at old
    cases outcome with
    | error reason => exact old
    | ok value => exact (after value k).trans old

theorem Quiet.forIn (items : List α) (initial : β)
    (body : α → β → PrefixOuter E (ForInStep β))
    (quiet : ∀ item state, Quiet (body item state)) :
    Quiet (ForIn.forIn items initial body) := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn_nil] using Quiet.pure initial
  | cons item items ih =>
    rw [List.forIn_cons]
    apply Quiet.bind (quiet item initial)
    intro step
    cases step with
    | done state => exact Quiet.pure state
    | yield state => exact ih state

theorem Quiet.array (items : Array α) (initial : β)
    (body : α → β → PrefixOuter E (ForInStep β))
    (quiet : ∀ item state, Quiet (body item state)) :
    Quiet (ForIn.forIn items initial body) := by
  rw [←Array.forIn_toList]
  exact Quiet.forIn _ _ _ quiet

theorem Quiet.native (index : Nat) (w : World) (action : Leanux.M α) :
    Quiet (runAtPrefix (Event:=E) index w (liftPrefix action)) := fun _ => rfl

open Lean Meta Elab Tactic in
elab "runner_quiet_head " name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Quiet do throwError "not a quiet runner action"
  let action := target.getAppArgs.back!.consumeMData
  let some actual := action.getAppFn.constName? | throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different action"

macro "runner_quiet_step" : tactic => `(tactic| first
  | (runner_quiet_head runAtPrefix; exact Quiet.native _ _ _)
  | (runner_quiet_head Pure.pure; exact Quiet.pure _)
  | (runner_quiet_head throw; exact Quiet.stopped _)
  | (runner_quiet_head Bind.bind; apply Quiet.bind)
  | (runner_quiet_head ForIn.forIn; first | apply Quiet.array | apply Quiet.forIn)
  | maintenance_intro
  | (dsimp (config := {failIfUnchanged := true}) only)
  | (split))

theorem afterCall_quiet (op : Operation) (state : RunnerOperation.State) (ret : Int) (w : World) :
    Quiet (E:=E) (RunnerOperation.afterCall op state ret w) := by
  unfold RunnerOperation.afterCall
  repeat' runner_quiet_step

theorem finish_quiet (trace : Trace) (state : RunnerOperation.State) :
    Quiet (E:=E) (RunnerOperation.finishWith (fun j v => (j,v)) trace state) := by
  unfold RunnerOperation.finishWith
  repeat' runner_quiet_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
