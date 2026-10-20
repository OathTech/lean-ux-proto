import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxCleanupSource

/-! Ordinary cleanup retains the sending ledger and consumes only the freed
cell's existing debt. Its source points acquire their accounts from entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch HandshakeSecurity.StagedConservation CompleteCarrier
open Staged.Obligations
variable {initial : Ledger}

theorem boundary_accounted (before : Accounted h initial [] locals w.wg)
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (completed : runPrefix (completion pid items) u middle=(.ok ((),v),last))
    (shape : items=done++rest)
    (leading : runPrefix (freeLoop cleanupOps done) v last=(.ok ((),q),after)) :
    ∃ledger debts,Staged.Obligations.Step initial ledger ∧
      Accounted after ledger debts (⟨.selected,pid,rest⟩::locals) q.wg := by
  have selection:=selection_returned before selected
  obtain ⟨context,peer,localEq,_,_,ledger,debts,_,_,settlements,path⟩:=
    OrdinaryCleanup.selected_cleanup_path selection completed
  rw [shape] at path
  obtain ⟨r,events,cutDebts,performed,account⟩:=path.accounted_cut done
  have same:=performed.symm.trans leading
  simp only [Prod.mk.injEq,Except.ok.injEq] at same
  obtain ⟨⟨_,rfl⟩,rfl⟩:=same
  exact ⟨ledger,cutDebts,settlements.step,by simpa only [peer,localEq] using account⟩

theorem primitive_accounted (before : Accounted h initial [] locals w.wg)
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (completed : runPrefix (completion pid items) u middle=(.ok ((),v),last))
    (shape : items=done++skb::rest)
    (leading : runPrefix (freeLoop cleanupOps done) v last=(.ok ((),q),after))
    (native : (liftWG (freeTxSkb skb)).run q=.ok ((),r)) (phase : CleanupPrimitive.Phase) :
    ∃ledger debts,Staged.Obligations.Step initial ledger ∧
      Accounted (CleanupPrimitive.current phase q skb after) ledger debts
        (⟨.selected,pid,rest⟩::locals) r.wg := by
  have selection:=selection_returned before selected
  obtain ⟨context,peer,localEq,_,_,ledger,debts,_,_,settlements,path⟩:=
    OrdinaryCleanup.selected_cleanup_path selection completed
  rw [shape] at path
  obtain ⟨cutWorld,cutHistory,cutDebts,generation,nextWorld,performed,interval,_⟩:=
    OrdinaryCleanup.prefix_interval done path
  have same:=performed.symm.trans leading
  simp only [Prod.mk.injEq,Except.ok.injEq] at same
  obtain ⟨⟨_,rfl⟩,rfl⟩:=same
  have sameWorld:=interval.native.symm.trans native
  simp only [Except.ok.injEq,Prod.mk.injEq] at sameWorld
  obtain ⟨_,rfl⟩:=sameWorld
  exact ⟨ledger,_,settlements.step,by simpa only [peer,localEq] using interval.accounted phase⟩

def Evidence (initial : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (h : List CausalJournal.Event) (w : World) : Prop :=
  ∃ledger debts rest,Staged.Obligations.Step initial ledger ∧
    Accounted h ledger debts (⟨.selected,pid,rest⟩::locals) w.wg

/-- Security: every fixed ordinary-cleanup cut retains the first terminal
ledger from sending. Native erasure consumes the existing cell debt; access
markers do not create a second disposition. -/
theorem Point.evidence (before : Accounted h initial [] locals w.wg)
    (point : Point pid w h u middle) : Evidence initial locals pid middle u := by
  cases point with
  | boundary selected completed shape leading=>
    obtain ⟨ledger,debts,steps,account⟩:=boundary_accounted before selected completed shape leading
    exact ⟨ledger,debts,_,steps,account⟩
  | primitive selected completed shape leading native phase=>
    obtain ⟨ledger,debts,steps,account⟩:=primitive_accounted before selected completed shape leading native phase
    exact ⟨ledger,debts,_,steps,account⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxCleanup
