import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalDebtCleanup
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalDispose

/-! A named create/DEAD free both settles and removes the physical cell. The
temporary debt is discharged by that same native free, so converse coverage
and mixed uniqueness survive alongside the immutable terminal ledger entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- The actual labelled free settles this allocation and discharges its
physical obligation. Its original branch reason remains the first outcome;
all surviving pending cells and terminal debts keep their fixed tickets. -/
theorem labelled_debt (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history suffix : List CausalJournal.Event)
    (performed : runPrefix (cleanupFree skb) w history = (.ok ((),v),history ++ suffix))
    (support : Support births history ledger debts w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
    let before := history ++ suffix
    let outcome := Staged.Obligations.Terminal.disposed before.length reason
    let after := settle [ticket] outcome ledger
    let debt : CleanupDebt := ⟨ticket,position,ordinal,outcome⟩
    let afterDebts := forgetFreedCell before generation skb (debt :: debts)
    let journal := before ++ [CausalJournal.Event.terminalDrop receipt]
    runPrefix (Terminal.freeObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.terminalDrop reason skb) w history = (.ok ((),v),journal) ∧
      Staged.Obligations.Step ledger after ∧ Support births journal after afterDebts v.wg ∧
      (ticket,Status.terminal outcome) ∈ after ∧ debt ∉ afterDebts ∧
      PacketMaterial.view v.wg skb = none := by
  dsimp only
  obtain ⟨native,observed⟩ := labelled_cut reason skb w v history suffix performed
  let outcome := Staged.Obligations.Terminal.disposed (history ++ suffix).length reason
  let debt : CleanupDebt := ⟨ticket,position,ordinal,outcome⟩
  have atEntry := support.append suffix
  obtain ⟨step,settled,_⟩ := atEntry.settle pending outcome
  have selected := (support.resident ticket position ordinal pending).at_origin origin
  obtain ⟨resident,mixed,covered,cleanup,terminal,removed⟩ := cleanup_native_mixed native
    settled.valid settled.mixed settled.resident settled.covered settled.cleanup debt
    (List.mem_cons_self ..) (origin.append suffix) selected.1
  have after : Support births (history ++ suffix) (settle [ticket] outcome ledger)
      (forgetFreedCell (history ++ suffix) generation skb (debt :: debts)) v.wg :=
    ⟨⟨resident,covered,cleanup,mixed⟩,settled.valid⟩
  exact ⟨observed,step,after.append _,terminal,removed,(native_free_views skb w v native).2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
