import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxDeadSource

/-! Entry accounting derives the exact successor ledger at every fixed
DEAD-loop boundary and the pending receipt at each native erase interval. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxDead
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation CompleteCarrier
open Staged.Obligations

theorem boundary_path (before : Accounted h ledger [] locals w.wg)
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle))
    (bound : n ≤ items.length)
    (leading : runPrefix (loop (.deadBatch pid head) (items.take n)) u middle=(.ok ((),v),last)) :
    ∃next,DeadIntervals.Path (.deadBatch pid head) pid [] locals n items u middle ledger v last next := by
  have selection:=selection_returned before selected
  obtain ⟨_,_,_,full⟩:=DeadIntervals.total (.deadBatch pid head) items
    selection.accounted_entry.1 selection.accounted_entry.2
  obtain ⟨q,after,next,path,_⟩:=full.split n bound
  have same:=path.run.symm.trans leading
  simp only [Prod.mk.injEq,Except.ok.injEq] at same
  obtain ⟨⟨_,rfl⟩,rfl⟩:=same
  exact ⟨next,path⟩

theorem primitive_waiting (before : Accounted h ledger [] locals w.wg)
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,false⟩,u),middle))
    (leading : runPrefix (loop (.deadBatch pid head) (items.take n)) u middle=(.ok ((),v),last))
    (dropped : items.drop n=skb::remaining)
    (native : (liftWG (freeTxSkb skb)).run v=.ok ((),q)) (phase : CleanupPrimitive.Phase) :
    ∃next after,Staged.Obligations.Step ledger next ∧
      CleanupPrimitive.Awaiting phase (.deadBatch pid head) pid [] locals skb remaining v last next q after := by
  have bound : n ≤ items.length := by
    have length:=congrArg List.length dropped
    simp only [List.length_drop,List.length_cons] at length
    omega
  obtain ⟨next,path⟩:=boundary_path before selected bound leading
  have atCut:=path.result.2.1
  have pending:=path.result.2.2
  rw [dropped] at atCut pending
  obtain ⟨r,after,settled,iteration⟩:=DeadIntervals.iteration_total (.deadBatch pid head) skb atCut pending
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,valid⟩:=iteration.settlement
  have actual : (liftWG (freeTxSkb skb)).run v=.ok ((),r):=valid
  have same:=actual.symm.trans native
  simp only [Except.ok.injEq,Prod.mk.injEq] at same
  obtain ⟨_,rfl⟩:=same
  exact ⟨next,settled,path.result.1,CleanupPrimitive.iteration_awaiting phase iteration⟩

inductive Evidence (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId) :
    List CausalJournal.Event → World → Prop where
  | boundary (next : Ledger) (items : List SkbId) (step : Staged.Obligations.Step ledger next)
      (account : Accounted h next [] (⟨.selected,pid,items⟩::locals) w.wg)
      (pending : PendingBatch h next items) : Evidence ledger locals pid h w
  | primitive (step : Staged.Obligations.Step ledger next)
      (waiting : CleanupPrimitive.Awaiting phase (.deadBatch pid head) pid [] locals skb remaining
        w h next v after) : Evidence ledger locals pid (CleanupPrimitive.current phase w skb h) v

/-- Security: each actual DEAD cleanup cut conserves the same allocated
lineage. A native erase is represented by its exact pending receipt until
the fixed total suffix records the terminal disposition. -/
theorem Point.evidence (before : Accounted h ledger [] locals w.wg)
    (point : Point pid w h u middle) : Evidence ledger locals pid middle u := by
  cases point with
  | boundary selected bound leading=>
    obtain ⟨next,path⟩:=boundary_path before selected bound leading
    exact .boundary next _ path.result.1 path.result.2.1 path.result.2.2
  | primitive selected leading dropped native phase=>
    obtain ⟨next,after,step,waiting⟩:=primitive_waiting before selected leading dropped native phase
    exact .primitive step waiting

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxDead
