import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalCleanup

/-! The create-refusal and DEAD source callbacks attach their real branch
reason to each native free. This cut is distinct from ordinary completion
cleanup, whose first terminal already occurred at the socket or refusal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- The actual branch-labelled wrapper records the completed atomic free
immediately. A later key or peer release may Stop without erasing this cut. -/
theorem labelled_cut (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history suffix : List CausalJournal.Event)
    (performed : runPrefix (cleanupFree skb) w history = (.ok ((),v),history ++ suffix)) :
    let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
    receipt.Valid ∧
      runPrefix (Terminal.freeObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.terminalDrop reason skb) w history =
          (.ok ((),v),(history ++ suffix) ++ [.terminalDrop receipt]) := by
  dsimp only
  refine ⟨(cleanupFree_erases skb w history).symm.trans (congrArg Prod.fst performed),?_⟩
  exact Terminal.observed_completed CausalJournal.Event.terminalDrop (cleanupFree skb)
    reason skb w v history (history ++ suffix) performed

/-- A real labelled native free settles the exact pending allocation and
removes its physical cell. The caller still supplies the actual branch reason
and entry carrier; the result assumes no initialized conservation theorem. -/
theorem labelled_settlement (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history suffix : List CausalJournal.Event)
    (performed : runPrefix (cleanupFree skb) w history = (.ok ((),v),history ++ suffix))
    (valid : Valid births ledger) (resident : Resident history ledger w.wg)
    (injective : Injective history ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value) :
    let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
    let outcome := Staged.Obligations.Terminal.disposed (history ++ suffix).length reason
    let after := settle [ticket] outcome ledger
    let journal := (history ++ suffix) ++ [CausalJournal.Event.terminalDrop receipt]
    runPrefix (Terminal.freeObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.terminalDrop reason skb) w history = (.ok ((),v),journal) ∧
      Staged.Obligations.Step ledger after ∧ Valid births after ∧
      Resident journal after v.wg ∧ Injective journal after ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      PacketMaterial.view v.wg skb = none := by
  dsimp only
  obtain ⟨native,observed⟩ := labelled_cut reason skb w v history suffix performed
  have result := dispose _ native valid (resident.append suffix) (injective.append resident suffix)
    pending (origin.append suffix)
  exact ⟨observed,result.1,result.2.1,result.2.2.1,result.2.2.2.1,
    result.2.2.2.2.1,result.2.2.2.2.2.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
