import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateDisposalSource

/-! The actual refusal free loop consumes a distinct pending native batch.
Each completed iteration settles the same allocation at its own labelled cut.
Under the explicit backed-batch input no free can Stop; later stopped
continuations retain every receipt without requiring their completion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

theorem loop_cons (reason : Terminal.Reason) (id : SkbId) (items : List SkbId) :
    loop reason (id :: items) = (do free reason id; loop reason items) := by
  simp only [loop,List.forIn_cons,bind_assoc,pure_bind]

/-- Native distinctness and pending backing discharge every actual free,
preserving all surviving pending/debt coverage and every first outcome. -/
theorem loop_total (reason : Terminal.Reason) (items : List SkbId)
    (unique : items.Nodup)
    (support : FirstTerminal.Support births history ledger debts w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ v suffix after afterDebts,
      runPrefix (loop reason items) w history = (.ok ((),v),history ++ suffix) ∧
      Staged.Obligations.Step ledger after ∧
      FirstTerminal.Support births (history ++ suffix) after afterDebts v.wg ∧
      AllDropped (history ++ suffix) after reason items := by
  induction items generalizing w history ledger debts with
  | nil =>
    refine ⟨w,[],ledger,debts,?_,.refl ledger,?_,?_⟩
    · simp [loop,runPrefix_pure]
    · simpa only [List.append_nil] using support
    · intro id member
      cases member
  | cons id items ih =>
    obtain ⟨absent,uniqueTail⟩ := List.nodup_cons.mp unique
    obtain ⟨ticket,position,ordinal,generation,value,member,origin⟩ := pending id (List.mem_cons_self ..)
    have rest : PendingBatch history ledger items :=
      fun other belongs => pending other (List.mem_cons_of_mem _ belongs)
    obtain ⟨u,middle,assigned,assignedDebts,first,step,kept,dropped,outcome,equal⟩ :=
      free_total reason id support member origin
    have remaining : PendingBatch (history ++ middle) assigned items := by
      rw [equal]
      exact (rest.settle_other support.valid member origin absent outcome).append middle
    obtain ⟨v,suffix,after,afterDebts,last,steps,final,done⟩ := ih uniqueTail kept remaining
    refine ⟨v,middle ++ suffix,after,afterDebts,?_,step.trans steps,?_,?_⟩
    · rw [loop_cons,runPrefix_bind,first]
      simpa only [List.append_assoc] using last
    · simpa only [List.append_assoc] using final
    · intro other belongs
      rcases List.mem_cons.mp belongs with same | later
      · subst other
        simpa only [List.append_assoc] using dropped.transport suffix steps
      · simpa only [List.append_assoc] using done other later

/-- The real labelled cuts remain visible through any later append-only
continuation, including its first Stop. No completed outer caller is assumed. -/
theorem loop_retained (reason : Terminal.Reason) (items : List SkbId)
    (unique : items.Nodup)
    (support : FirstTerminal.Support births history ledger debts w.wg)
    (pending : PendingBatch history ledger items)
    (next : PrefixM CausalJournal.Event α) (appends : Appends next) :
    ∃ after, Staged.Obligations.Step ledger after ∧
      AllDropped (runPrefix (do loop reason items; next) w history).2 after reason items := by
  obtain ⟨v,suffix,after,afterDebts,performed,step,_,done⟩ := loop_total reason items unique support pending
  obtain ⟨later,grown⟩ := appends v (history ++ suffix)
  refine ⟨after,step,?_⟩
  rw [runPrefix_bind,performed]
  change AllDropped (runPrefix next v (history ++ suffix)).2 after reason items
  rw [grown]
  exact done.transport later (.refl after)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
