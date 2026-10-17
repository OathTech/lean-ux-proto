import Leanux.Proofs.WG.Progress.PollLoopSource
import Leanux.Proofs.WG.Progress.PollBoundEffects

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Noise Roaming Campaign2 Std.Do

/-- The original zero-budget test and whole loop, cut before completion. -/
def pollBoundPrefix (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) : Leanux.M (Option PollState) := do
  if ← branch .rxPollNoBudget (budget == 0) then return none
  let state ← forIn ([:MAX_QUEUED_PACKETS + 1] : Std.Legacy.Range)
    ((0, {}, false) : PollState) (pollStep pid budget toStack)
  return some state

def pollBoundSuffix (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) : Option PollState → Leanux.M Nat
  | none => pure 0
  | some state => pollFinish pid budget toStack state

/-- Full computation equality, including all original callback errors. -/
theorem rxPoll_bound_source (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    rxPoll pid budget toStack =
      (pollBoundPrefix pid budget toStack >>= pollBoundSuffix pid budget toStack) := by
  rw [rxPoll_source]
  simp only [pollBoundPrefix, bind_assoc]
  congr 1
  funext zero
  cases zero <;> simp [pollBoundSuffix]

theorem pollBoundPrefix_ready (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (enough : budget ≤ MAX_QUEUED_PACKETS + 1) :
    Noise.Product.Ensures (pollBoundPrefix pid budget toStack) (fun _ => True)
      (fun result _ => match result with
        | none => budget = 0
        | some state => budget ≠ 0 ∧ PollLoopReady budget state) := by
  intro entry result final pre run
  let tested := { entry with ambient := {entry.ambient with
    steps := entry.ambient.steps.push { decision := .rxPollNoBudget, outcome := budget == 0, netRx := entry.ambient.netRxSection } }}
  have test : (branch .rxPollNoBudget (budget == 0) : Leanux.M Bool).run entry =
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
    (toStack : List (List UInt8) → Leanux.M Unit) (state : PollState) :
    Noise.Product.Ensures (pollFinish pid budget toStack state) (fun _ => True)
      (fun result _ => result = state.1 ∧ result < budget) := by
  have any {α : Type} (a : Leanux.M α) :
      Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) := by
    intro w x out pre run
    trivial
  unfold pollFinish
  dsimp only
  split
  · intro w result out pre run
    cases run
  · refine Noise.Product.ensures_bind (Q := fun complete _ => complete = decide (state.1 < budget))
      _ _ ?_ ?_
    · intro w result out pre run
      let step : Step := {decision := .rxPollComplete, outcome := decide (state.1 < budget), netRx := w.ambient.netRxSection}
      change Except.ok (decide (state.1 < budget),
        {w with ambient := {w.ambient with steps := w.ambient.steps.push step}}) = _ at run
      cases run
      rfl
    · intro complete w result out pre run
      subst complete
      by_cases below : state.1 < budget
      · simp only [below, decide_true, ite_true] at run
        have finish : Noise.Product.Ensures (do
            let p ← (monadLift (getPeer pid) : Leanux.M Peer)
            monadLift (setPeer pid {p with napiScheduled := false})
            napiGroFlushAll toStack state.2.1
            pure state.1) (fun _ => True)
            (fun result _ => result = state.1 ∧ result < budget) := by
          refine Noise.Product.ensures_bind _ _ (any _) (fun p => ?_)
          refine Noise.Product.ensures_bind _ _ (any _) (fun _ => ?_)
          refine Noise.Product.ensures_bind _ _ (any _) (fun _ => ?_)
          intro entry value final pre normal
          cases normal
          exact ⟨rfl, below⟩
        exact finish w result out trivial run
      · simp only [below, decide_false, Bool.false_eq_true, ite_false] at run
        cases run

/-- The actual prefix and completion run sequentially on the same original
states. Prefix errors remain prefix errors; completion errors retain their cut. -/
def pollBoundAuditRun (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (entry : World) : PollBoundAudit :=
  match (pollBoundPrefix pid budget toStack).run entry with
  | .error error => .prefixError error
  | .ok (none, final) => .zero (Product.snapshot final)
  | .ok (some state, before) =>
    .finish state (Product.snapshot before) (Product.observeResult ((pollFinish pid budget toStack state).run before))

def observedPollBound (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) : Leanux.M PollBoundAudit := fun entry =>
  .ok (pollBoundAuditRun pid budget toStack entry, entry)

theorem pollBoundAuditRun_erases (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (entry : World) :
    erasePollBoundAudit (pollBoundAuditRun pid budget toStack entry) =
      Product.observeResult ((rxPoll pid budget toStack).run entry) := by
  rw [rxPoll_bound_source, StateT.run_bind]
  unfold pollBoundAuditRun
  cases hp : (pollBoundPrefix pid budget toStack).run entry with
  | error error => rfl
  | ok pair =>
    obtain ⟨choice, middle⟩ := pair
    cases choice <;> rfl

theorem observedPollBound_source (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    (do let audit ← observedPollBound pid budget toStack
        pure (erasePollBoundAudit audit)) = Product.inspect (rxPoll pid budget toStack) := by
  funext entry
  change Except.ok (erasePollBoundAudit (pollBoundAuditRun pid budget toStack entry), entry) = _
  rw [pollBoundAuditRun_erases]
  rfl

theorem pollBoundAuditRun_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (enough : budget ≤ MAX_QUEUED_PACKETS + 1)
    (entry : World) : PollBoundFacts budget (pollBoundAuditRun pid budget toStack entry) := by
  unfold pollBoundAuditRun
  cases hp : (pollBoundPrefix pid budget toStack).run entry with
  | error error => trivial
  | ok pair =>
    obtain ⟨choice, before⟩ := pair
    have prefixFacts := pollBoundPrefix_ready pid budget toStack enough entry choice before trivial hp
    cases choice with
    | none => exact prefixFacts
    | some state =>
      obtain ⟨positive, ready⟩ := prefixFacts
      refine ⟨positive, ready, pollLoopReady_not_drained budget state ready, ?_⟩
      intro n final completed
      cases finish : (pollFinish pid budget toStack state).run before with
      | error error => simp [Product.observeResult, finish, Except.map] at completed
      | ok pair =>
        obtain ⟨result, after⟩ := pair
        have count := pollFinish_normal_count pid budget toStack state before result after trivial finish
        simp only [Product.observeResult, finish, Except.map] at completed
        have same : result = n := congrArg Prod.fst (Except.ok.inj completed)
        simpa [same] using count

end Leanux.Proofs.WG.Progress
