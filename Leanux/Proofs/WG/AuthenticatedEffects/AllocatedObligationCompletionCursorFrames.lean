import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFrontier

/-! Native branch records and transparent scopes preserve the active local
cursor. Switching from sends to frees retains every terminal as cleanup debt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CompletionCuts

theorem State.append (before : State context phase history w) (suffix : List CausalJournal.Event) :
    State context phase (history ++ suffix) w := by
  obtain ⟨ledger,debts,step,support,recorded,remaining,assigned,coverage,inventory⟩ := before
  exact ⟨ledger,debts,step,support.append suffix,
    fun binding member => (recorded binding member).append suffix,
    remaining,assigned,coverage,inventory⟩

theorem State.sameWG (before : State context phase history w) (same : v.wg = w.wg) :
    State context phase history v := by
  unfold State at before ⊢
  simpa only [same] using before

theorem State.ready_to_free (before : State context (.sending []) history w) :
    State context (.freeing context.items) history w := by
  obtain ⟨ledger,debts,step,support,recorded,_,assigned,coverage,inventory⟩ := before
  refine ⟨ledger,debts,step,support,recorded,⟨[],rfl⟩,?_,coverage,inventory⟩
  intro binding member
  obtain ⟨outcome,debt,terminal⟩ := (assigned binding member).2 (by simp)
  exact ⟨⟨outcome,terminal⟩,fun _ => ⟨outcome,debt,terminal⟩⟩

theorem branch_run (decision : Decision) (value : Bool) (w : World)
    (history : List CausalJournal.Event) :
    runPrefix (CausalJournal.completionOps.step (branch decision value)) w history =
      (.ok (value,{w with ambient := CounterWindow.record w.ambient decision value}),history) := by
  change runPrefix (focusPrefix _ _ (liftPrefix (liftWG (branch decision value)))) w history = _
  apply (focusPrefix_suffix _ _ _ w history
    (.ok (value,{w with ambient := CounterWindow.record w.ambient decision value})) []
    (by simp only [List.append_nil]; rfl)).trans
  simp

/-- Native branch bookkeeping is total and changes only ambient records;
the concrete active batch and fixed ledger remain at the same cursor. -/
theorem branch_checked (decision : Decision) (value : Bool) (context : Context) (phase : Phase)
    (fact : Prop) :
    Ensures (fun h w => State context phase h w ∧ fact) (Stopped context)
      (CausalJournal.completionOps.step (branch decision value))
      (fun _ h w => State context phase h w ∧ fact) := by
  intro w history before
  rw [branch_run]
  exact ⟨[],by simp, before.1.sameWG rfl,before.2⟩

theorem branch_state (decision : Decision) (value : Bool) (context : Context) (phase : Phase) :
    Ensures (State context phase) (Stopped context)
      (CausalJournal.completionOps.step (branch decision value))
      (fun _ => State context phase) := by
  intro w history before
  rw [branch_run]
  exact ⟨[],by simp,before.sameWG rfl⟩

theorem scoped_checked (context : Context) (input output : Phase) (cause : CausalSources.Cause)
    (body : PrefixM CausalJournal.Event α)
    (checked : Ensures (State context input) (Stopped context) body (fun _ => State context output)) :
    Ensures (State context input) (Stopped context)
      (CausalScope.prefixScope CausalJournal.Event.scope cause (fun _ => body))
      (fun _ => State context output) := by
  intro w history before
  let entry := CausalJournal.Event.scope (.entered ⟨history.length,cause⟩)
  obtain ⟨suffix,grown,result⟩ := checked w (history ++ [entry]) (before.append [entry])
  rw [CausalScope.prefix_run]
  cases run : runPrefix body w (history ++ [entry]) with
  | mk outcome after =>
    simp only [run] at grown result
    cases outcome with
    | error reason =>
      exact ⟨entry :: suffix,by simpa only [List.append_assoc,List.singleton_append] using grown,result⟩
    | ok value =>
      refine ⟨entry :: (suffix ++ [CausalJournal.Event.scope (.exited history.length)]),?_,?_⟩
      · simp only [grown,List.append_assoc,List.cons_append,List.nil_append]
      · exact result.append _

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
