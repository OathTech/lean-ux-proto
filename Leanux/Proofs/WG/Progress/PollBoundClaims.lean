import Leanux.Proofs.WG.Progress.PollBoundSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Roaming Campaign2

theorem pollBoundAuditRun_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (enough : budget ≤ MAX_QUEUED_PACKETS + 1)
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
      | error error => simp [observeResult, finish, Except.map] at completed
      | ok pair =>
        obtain ⟨result, after⟩ := pair
        have count := pollFinish_normal_count pid budget toStack state before result after trivial finish
        simp only [observeResult, finish, Except.map] at completed
        have same : result = n := congrArg Prod.fst (Except.ok.inj completed)
        simpa [same] using count

/-- Inspection's returned datum certifies the actual original loop boundary;
its own unchanged entry state is not a claimed successful poll final state. -/
theorem source_poll_bound (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (enough : budget ≤ MAX_QUEUED_PACKETS + 1) :
    Campaign2.Returns (observedPollBound pid budget toStack) (fun _ => True)
      (fun audit _ => PollBoundFacts budget audit) := by
  intro entry pre
  exact ⟨pollBoundAuditRun pid budget toStack entry, entry, rfl,
    pollBoundAuditRun_facts pid budget toStack enough entry⟩

end Leanux.Proofs.WG.Progress
