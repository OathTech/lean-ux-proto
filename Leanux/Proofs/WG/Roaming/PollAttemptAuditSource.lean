import Leanux.Proofs.WG.Roaming.PollAttemptSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Campaign2

/-- Execute admission once, then the original suffix at that successor. The
iteration record is retained even when either phase stops. -/
def pollAttemptStepRun (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (state : PollState) (entry : World) :
    PollAttemptIteration × Except Stop (ForInStep PollState × World) :=
  match (pollAttemptPrefix pid).run entry with
  | .error error =>
    (⟨snapshot entry, .error error, none⟩, .error error)
  | .ok (prepared, before) =>
    let result := (pollAttemptSuffix pid budget toStack state prepared).run before
    (⟨snapshot entry, .ok (prepared, snapshot before), some (observeResult result)⟩, result)

/-- One record per attempted iteration, with the actual state threaded through
all callbacks. A done step or error stops this same original loop. -/
def pollAttemptLoopRun (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) :
    List Nat → PollState → World → List PollAttemptIteration × Except Stop (PollState × World)
  | [], state, entry => ([], .ok (state, entry))
  | _ :: turns, state, entry =>
    let step := pollAttemptStepRun pid budget toStack state entry
    match step.2 with
    | .error error => ([step.1], .error error)
    | .ok (.done final, out) => ([step.1], .ok (final, out))
    | .ok (.yield next, middle) =>
      let tail := pollAttemptLoopRun pid budget toStack turns next middle
      (step.1 :: tail.1, tail.2)

theorem pollAttemptStepRun_erases (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (turn : Nat) (state : PollState) (entry : World) :
    (pollAttemptStepRun pid budget toStack state entry).2 =
      (pollStep pid budget toStack turn state).run entry := by
  rw [pollStep_attempt_source, StateT.run_bind]
  unfold pollAttemptStepRun
  cases h : (pollAttemptPrefix pid).run entry with
  | error error => rfl
  | ok pair => obtain ⟨prepared, before⟩ := pair; rfl

/-- Completeness of one loop step: its admission/continuation record is always
the head, including a pre-setter cut whose continuation failed. -/
theorem pollAttemptLoopRun_head (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (turn : Nat) (turns : List Nat)
    (state : PollState) (entry : World) :
    (pollAttemptLoopRun pid budget toStack (turn :: turns) state entry).1.head? =
      some (pollAttemptStepRun pid budget toStack state entry).1 := by
  simp only [pollAttemptLoopRun]
  cases h : (pollAttemptStepRun pid budget toStack state entry).2 with
  | error error => rfl
  | ok pair => obtain ⟨step, out⟩ := pair; cases step <;> rfl

/-- A reached endpoint case is recorded before the suffix is inspected;
there is no successful-suffix premise. -/
theorem pollAttemptStepRun_endpoint (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (state : PollState) (entry before : World)
    (cut : PollAttemptCut)
    (reached : (pollAttemptPrefix pid).run entry = .ok (.endpoint cut, before)) :
    (pollAttemptStepRun pid budget toStack state entry).1 =
      ⟨snapshot entry, .ok (.endpoint cut, snapshot before),
       some (observeResult ((pollAttemptSuffix pid budget toStack state (.endpoint cut)).run before))⟩ := by
  simp only [pollAttemptStepRun, reached]

theorem pollAttemptLoopRun_erases (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (turns : List Nat) (state : PollState) (entry : World) :
    (pollAttemptLoopRun pid budget toStack turns state entry).2 =
      (forIn turns state (pollStep pid budget toStack)).run entry := by
  induction turns generalizing state entry with
  | nil => rfl
  | cons turn turns ih =>
    rw [List.forIn_cons, StateT.run_bind, ← pollAttemptStepRun_erases]
    simp only [pollAttemptLoopRun]
    cases h : (pollAttemptStepRun pid budget toStack state entry).2 with
    | error error => rfl
    | ok pair =>
      obtain ⟨step, out⟩ := pair
      cases step with
      | done next => rfl
      | yield next => exact ih next out

/-- The original budget test and completion surround the audited whole loop. -/
def pollAttemptAuditRun (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (entry : World) : PollAttemptAudit :=
  match (branch .rxPollNoBudget (budget == 0)).run entry with
  | .error error => ⟨[], .error error⟩
  | .ok (zero, afterTest) =>
    if zero then ⟨[], .ok (0, snapshot afterTest)⟩
    else
      let loop := pollAttemptLoopRun pid budget toStack
        (List.range' 0 (MAX_QUEUED_PACKETS + 1)) (0, {}, false) afterTest
      ⟨loop.1, observeResult (loop.2 >>= fun (state, beforeFinish) =>
        (pollFinish pid budget toStack state).run beforeFinish)⟩

def observedPollAttempts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) : M PollAttemptAudit := fun entry =>
  .ok (pollAttemptAuditRun pid budget toStack entry, entry)

theorem pollAttemptAuditRun_erases (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (entry : World) :
    (pollAttemptAuditRun pid budget toStack entry).outcome =
      observeResult ((rxPoll pid budget toStack).run entry) := by
  rw [rxPoll_source]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.zero_add, Nat.sub_zero, Nat.div_one]
  simp only [StateT.run_bind, pollAttemptAuditRun]
  cases h : (branch .rxPollNoBudget (budget == 0)).run entry with
  | error error => rfl
  | ok pair =>
    obtain ⟨zero, afterTest⟩ := pair
    cases zero with
    | true => rfl
    | false => simp only [Bool.false_eq_true, ite_false, pollAttemptLoopRun_erases]; rfl

theorem observedPollAttempts_erase (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) :
    (do let audit ← observedPollAttempts pid budget toStack; pure audit.outcome) =
      inspect (rxPoll pid budget toStack) := by
  funext entry
  change Except.ok ((pollAttemptAuditRun pid budget toStack entry).outcome, entry) = _
  rw [pollAttemptAuditRun_erases]
  rfl

end Leanux.Proofs.WG.Roaming
