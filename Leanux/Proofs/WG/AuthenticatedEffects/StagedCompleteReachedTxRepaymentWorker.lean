import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxRepaymentFrames

/-! Both original cleanup arms enter the same repayment source. Entry
ownership is derived from selection and the actual completed free loop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxRepayment
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompleteCarrier Staged.Obligations
open CreateDisposal

inductive Entry (pid : PeerId) (w : World) (h : List CausalJournal.Event) :
    KeypairId → World → List CausalJournal.Event → Prop where
  | dead (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle))
      (freed : runPrefix (CreateDisposal.loop (.deadBatch pid head) items) u middle=(.ok ((),v),last)) :
      Entry pid w h head.keypair v last
  | crypted (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
      (completed : runPrefix (TxCleanup.completion pid items) u middle=(.ok ((),v),last))
      (freed : runPrefix (freeLoop cleanupOps items) v last=(.ok ((),q),after)) :
      Entry pid w h head.keypair q after

theorem Entry.continuation (entry : Entry pid w h key u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (action pid key) u middle := by
  cases entry with
  | dead selected freed=>rw [TxDead.selected_continuation selected,runPrefix_bind,freed]
  | crypted selected completed freed=>
    rw [TxCleanup.selected_continuation selected completed,runPrefix_bind,freed,ordinary_source]

theorem Entry.accounted (before : Accounted h ledger [] locals w.wg)
    (entry : Entry pid w h key u middle) :
    ∃next,Staged.Obligations.Step ledger next ∧ Accounted middle next [] locals u.wg := by
  cases entry with
  | dead selected freed=>
    have selection:=selection_returned before selected
    obtain ⟨v,last,next,full,performed,account,_⟩:=DeadIntervals.completed_intervals _ _
      selection.accounted_entry.1 selection.accounted_entry.2
    have same:=performed.symm.trans freed
    simp only [Prod.mk.injEq,Except.ok.injEq] at same
    obtain ⟨⟨_,rfl⟩,rfl⟩:=same
    exact ⟨next,full.result.1,account⟩
  | crypted selected completed freed=>
    have selection:=selection_returned before selected
    obtain ⟨context,peer,localEq,_,_,next,debts,v,last,settlements,path⟩:=
      OrdinaryCleanup.selected_cleanup_path selection completed
    have same:=path.run.symm.trans freed
    simp only [Prod.mk.injEq,Except.ok.injEq] at same
    obtain ⟨⟨_,rfl⟩,rfl⟩:=same
    have owned:=path.returned.1
    have account : Accounted _ next [] context.locals _:=
      ⟨empty_local .selected owned.entry,path.returned.2⟩
    exact ⟨next,settlements.step,by simpa only [localEq] using account⟩

inductive WorkerPoint (pid : PeerId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | repay (entry : Entry pid w h key u middle) (point : Point pid key u middle v last) : WorkerPoint pid w h v last

theorem WorkerPoint.remaining (point : WorkerPoint pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | repay entry point=>
    obtain ⟨remaining,continued⟩:=point.remaining
    exact ⟨remaining,entry.continuation.trans continued⟩

noncomputable def workerRemainder (point : WorkerPoint pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem workerRemainder_run (point : WorkerPoint pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (workerRemainder point) u middle :=
  Classical.choose_spec point.remaining

/-- Security: both actual worker disposal arms supply their own repayment
account. The resulting key or peer-retirement cut stays on a successor of
the same incoming packet ledger, without an assumed cleanup certificate. -/
theorem WorkerPoint.evidence (before : Accounted h ledger [] locals w.wg)
    (point : WorkerPoint pid w h u middle) :
    ∃next,Staged.Obligations.Step ledger next ∧ Evidence next [] locals middle u := by
  cases point with
  | repay entry point=>
    obtain ⟨next,steps,account⟩:=entry.accounted before
    exact ⟨next,steps,point.evidence account⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxRepayment
