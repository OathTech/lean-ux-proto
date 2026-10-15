import Leanux.Proofs.WG.Progress.PollLoopSource
import Leanux.Proofs.WG.Progress.PollBoundEffects

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Noise Roaming Campaign2 Std.Do

/-- The original zero-budget test and whole loop, cut before completion. -/
def pollBoundPrefix (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) : M (Option PollState) := do
  if ← branch .rxPollNoBudget (budget == 0) then return none
  let state ← forIn ([:MAX_QUEUED_PACKETS + 1] : Std.Legacy.Range)
    ((0, {}, false) : PollState) (pollStep pid budget toStack)
  return some state

def pollBoundSuffix (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) : Option PollState → M Nat
  | none => pure 0
  | some state => pollFinish pid budget toStack state

/-- Full computation equality, including all original callback errors. -/
theorem rxPoll_bound_source (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) :
    rxPoll pid budget toStack =
      (pollBoundPrefix pid budget toStack >>= pollBoundSuffix pid budget toStack) := by
  rw [rxPoll_source]
  simp only [pollBoundPrefix, bind_assoc]
  congr 1
  funext zero
  cases zero <;> simp [pollBoundSuffix]

theorem pollBoundPrefix_ready (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (enough : budget ≤ MAX_QUEUED_PACKETS + 1) :
    Noise.Ensures (pollBoundPrefix pid budget toStack) (fun _ => True)
      (fun result _ => match result with
        | none => budget = 0
        | some state => budget ≠ 0 ∧ PollLoopReady budget state) := by
  intro entry result final pre run
  let tested := { entry with
    steps := entry.steps.push { decision := .rxPollNoBudget, outcome := budget == 0, netRx := entry.netRxSection } }
  have test : (branch .rxPollNoBudget (budget == 0)).run entry =
      .ok (budget == 0, tested) := rfl
  rw [pollBoundPrefix, StateT.run_bind, test] at run
  dsimp only [Bind.bind, Except.bind] at run
  by_cases zero : budget = 0
  · subst budget
    change Except.ok (none, tested) = .ok (result, final) at run
    have choice : result = none := (congrArg Prod.fst (Except.ok.inj run)).symm
    rw [choice]
  · have negative : (budget == 0) = false := by simpa using zero
    rw [negative] at run
    change ((forIn ([:MAX_QUEUED_PACKETS + 1] : Std.Legacy.Range)
      ((0, {}, false) : PollState) (pollStep pid budget toStack)).run tested >>=
        fun pair => Except.ok (some pair.1, pair.2)) = .ok (result, final) at run
    cases loop : (forIn ([:MAX_QUEUED_PACKETS + 1] : Std.Legacy.Range)
        ((0, {}, false) : PollState) (pollStep pid budget toStack)).run tested with
    | error error => rw [loop] at run; cases run
    | ok pair =>
      obtain ⟨state, after⟩ := pair
      rw [loop] at run
      change Except.ok (some state, after) = .ok (result, final) at run
      have choice : result = some state := (congrArg Prod.fst (Except.ok.inj run)).symm
      rw [choice]
      exact ⟨zero, pollRange_ready pid budget toStack enough tested state after (by omega) loop⟩

theorem pollFinish_normal_count (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (state : PollState) :
    Noise.Ensures (pollFinish pid budget toStack state) (fun _ => True)
      (fun result _ => result = state.1 ∧ result < budget) := by
  have hg := poll_any_normal (getPeer pid)
  have hs := fun p => poll_any_normal (setPeer pid p)
  have hf := poll_any_normal (napiGroFlushAll toStack state.2.1)
  rw [ensures_iff]
  mvcgen [pollFinish, branch, invariant, unsupported, hg, hs, hf]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

/-- The actual prefix and completion run sequentially on the same original
states. Prefix errors remain prefix errors; completion errors retain their cut. -/
def pollBoundAuditRun (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (entry : World) : PollBoundAudit :=
  match (pollBoundPrefix pid budget toStack).run entry with
  | .error error => .prefixError error
  | .ok (none, final) => .zero (snapshot final)
  | .ok (some state, before) =>
    .finish state (snapshot before) (observeResult ((pollFinish pid budget toStack state).run before))

def observedPollBound (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) : M PollBoundAudit := fun entry =>
  .ok (pollBoundAuditRun pid budget toStack entry, entry)

theorem pollBoundAuditRun_erases (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (entry : World) :
    erasePollBoundAudit (pollBoundAuditRun pid budget toStack entry) =
      observeResult ((rxPoll pid budget toStack).run entry) := by
  rw [rxPoll_bound_source, StateT.run_bind]
  unfold pollBoundAuditRun
  cases hp : (pollBoundPrefix pid budget toStack).run entry with
  | error error => rfl
  | ok pair =>
    obtain ⟨choice, middle⟩ := pair
    cases choice <;> rfl

theorem observedPollBound_source (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) :
    (do let audit ← observedPollBound pid budget toStack
        pure (erasePollBoundAudit audit)) = inspect (rxPoll pid budget toStack) := by
  funext entry
  change Except.ok (erasePollBoundAudit (pollBoundAuditRun pid budget toStack entry), entry) = _
  rw [pollBoundAuditRun_erases]
  rfl

end Leanux.Proofs.WG.Progress
