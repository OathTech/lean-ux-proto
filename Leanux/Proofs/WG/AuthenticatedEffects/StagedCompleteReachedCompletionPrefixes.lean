import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCompletionCases

/-! Literal completion prefixes reach the matched stopped cut. Prelude and
finish stages are finite source labels; loop prefixes are the original loop
on its processed list, followed by the actual capture/socket prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {initial : Ledger}

inductive Point where
  | prelude (stage : PreludeStage)
  | packet (done : List SkbId) (skb : SkbId)
  | accounting (done : List SkbId) (skb : SkbId)
  | finish (stage : FinishStage)

def Point.InSource (context : Context) : Point → Prop
  | .packet done skb | .accounting done skb => ∃ rest, context.items = done ++ (skb :: rest)
  | .prelude _ | .finish _ => True

def sourcePrefix (context : Context) : Point → PrefixM CausalJournal.Event Unit
  | .prelude stage => fun w => ExceptT.mk fun history => runPrefix (do
      emitPrefix (Sending.entered context history)
      preludePrefix context stage) w history
  | .packet done skb => do
      _ ← Sending.scopedIterationPrefix context done
      _ ← Sending.iterationPrefix skb
      pure ()
  | .accounting done skb => do
      _ ← Sending.scopedIterationPrefix context done
      let packet ← Sending.iterationPrefix skb
      _ ← Sending.accountingPrefix context.pid skb packet
      pure ()
  | .finish stage => fun w => ExceptT.mk fun history => runPrefix (do
      emitPrefix (Sending.entered context history)
      Sending.prelude context
      let sent ← sendLoop CausalJournal.completionOps context.pid context.items false
      finishPrefix context sent stage) w history

private theorem trace_socket (trace : SendSettlements context initial original ledger debts)
    (before : Owned context (.sending (skb :: rest)) history ledger debts w)
    (chosen : Binding) (member : chosen ∈ context.bindings) (head : chosen.skb = skb)
    (position : Nat) (sent : Bool) :
    SendSettlements context initial original (settle [chosen.ticket] (.socket position sent) ledger)
      (⟨chosen.ticket,chosen.position,chosen.ordinal,.socket position sent⟩ :: debts) := by
  have pending := (before.cursor.assigned chosen member).1 (by simp [head])
  have support : FirstTerminal.Support (births history) history ledger debts w.wg :=
    ⟨before.entry.core.physical,before.entry.core.valid⟩
  exact trace.settle chosen member (.socket position sent) True.intro pending
    (support.settle pending (.socket position sent)).1

theorem ScopedStop.reached_cut
    (stopped : ScopedStop context initial original w history reason last) :
    ∃ point : Point, ∃ cut : Cut context, point.InSource context ∧ SendSettlements context initial original cut.ledger cut.debts ∧
      runPrefix (sourcePrefix context point) w history = (.ok ((),cut.world),cut.before) ∧
      cut.Valid reason last := by
  cases stopped with
  | prelude ledger debts trace stop =>
    refine ⟨.prelude stop.stage,passiveCut context (.sending context.items)
      (preludeSite context stop.stage) stop.world stop.before ledger debts,True.intro,trace,?_,stop.cut.valid⟩
    change runPrefix (do
      emitPrefix (Sending.entered context history)
      preludePrefix context stop.stage) w history = _
    simp only [runPrefix_bind,runPrefix_emit]
    exact stop.reached
  | loop u middle prepared stopped =>
    obtain ⟨done,skb,rest,next,v,cutHistory,ledger,debts,shape,iterations,trace,⟨iteration⟩⟩ := stopped.iteration_prefix
    have reached := Sending.scoped_iteration_run prepared iterations
    cases iteration.sendFailure with
    | pending stop =>
      refine ⟨.packet done skb,Cut.indexed stop.frontier,⟨rest,shape⟩,trace,?_,stop.matched.2.2.2.2⟩
      change runPrefix (do
        _ ← Sending.scopedIterationPrefix context done
        _ ← Sending.iterationPrefix skb
        pure ()) w history = (.ok ((),iteration.world),iteration.before)
      simp only [runPrefix_bind,reached,iteration.reached,runPrefix_pure]
    | accounting chosen member head position sent stop =>
      refine ⟨.accounting done skb,Cut.indexed stop.frontier,⟨rest,shape⟩,
        trace_socket trace iteration.owned chosen member head position sent,?_,stop.matched.2.2.2.2⟩
      change runPrefix (do
        _ ← Sending.scopedIterationPrefix context done
        let packet ← Sending.iterationPrefix skb
        _ ← Sending.accountingPrefix context.pid skb packet
        pure ()) w history = (.ok ((),stop.world),stop.history)
      simp only [runPrefix_bind,reached,iteration.reached,stop.reached,runPrefix_pure]
  | finish u middle prepared sent v after looped ledger debts trace stop =>
    refine ⟨.finish stop.stage,passiveCut context (.sending [])
      (finishSite context stop.stage) stop.world stop.before ledger debts,True.intro,trace,?_,stop.cut.valid⟩
    change runPrefix (do
      emitPrefix (Sending.entered context history)
      Sending.prelude context
      let flag ← sendLoop CausalJournal.completionOps context.pid context.items false
      finishPrefix context flag stop.stage) w history = _
    simp only [runPrefix_bind,runPrefix_emit,prepared,looped,stop.reached]
    rfl

/-- The actual completeScoped failure selects a fixed source prefix and the
same ledger/debt account, including post-socket accounting failures. -/
theorem completeScoped_stopped_cut
    (before : Converse.Sending context initial original context.items history w)
    (failed : runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
      CausalJournal.completionOps context.pid context.items) w history = (.error reason,last)) :
    ScopedStop context initial original w history reason last ∧
    ∃ point : Point, ∃ cut : Cut context, point.InSource context ∧ SendSettlements context initial original cut.ledger cut.debts ∧
      runPrefix (sourcePrefix context point) w history = (.ok ((),cut.world),cut.before) ∧
      cut.Valid reason last := by
  have stopped := scoped_failed before failed
  exact ⟨stopped,stopped.reached_cut⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
