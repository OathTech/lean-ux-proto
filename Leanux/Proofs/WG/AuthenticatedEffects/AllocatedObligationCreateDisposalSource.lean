import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateDisposalFrames

/-! Each pending backed native cell can actually be freed. The proof uses the
native allocator store and exact cleanup observer, then T4's labelled debt
settlement at the same source cut. No completed enclosing caller is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : SkbId}

theorem cleanup_total (cell : PacketMaterial.view w.wg id = some value)
    (history : List CausalJournal.Event) :
    ∃ v suffix, runPrefix (FirstTerminal.cleanupFree id) w history = (.ok ((),v),history ++ suffix) := by
  obtain ⟨packet,resident,_⟩ := Option.map_eq_some_iff.mp cell
  cases device : w.wg.dev with
  | none => simp [TxDisposition.txPackets,device] at resident
  | some d =>
    have found : d.txSkbs[id]? = some packet := by
      simpa [TxDisposition.txPackets,device] using resident
    let v := {w with wg := Packets.update w.wg (fun dev => {dev with txSkbs := dev.txSkbs.erase id})}
    have native : (liftWG (freeTxSkb id)).run w = .ok ((),v) := by
      rw [liftWG_run,Packets.freeTxSkb_run w.wg w.ambient d id packet device found]
      rfl
    have erased := (FirstTerminal.cleanupFree_erases id w history).trans native
    obtain ⟨suffix,grown⟩ := (show Appends (FirstTerminal.cleanupFree id) from Appends.focus _ _ _) w history
    exact ⟨v,suffix,Prod.ext erased grown⟩

/-- At this actual labelled source callback, the pending ticket receives the
native branch reason and its cell is removed. The source receipt stays at its
precise journal position and the same terminal is retained in the ledger. -/
theorem free_total (reason : Terminal.Reason) (id : SkbId)
    (support : FirstTerminal.Support births history ledger debts w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation id value) :
    ∃ v suffix after afterDebts,
      runPrefix (free reason id) w history = (.ok ((),v),history ++ suffix) ∧
      Staged.Obligations.Step ledger after ∧
      FirstTerminal.Support births (history ++ suffix) after afterDebts v.wg ∧
      Dropped (history ++ suffix) after reason id ∧
      ∃ outcome, after = settle [ticket] outcome ledger := by
  have selected := (support.resident ticket position ordinal pending).at_origin origin
  obtain ⟨v,middle,performed⟩ := cleanup_total selected.2 history
  have result := FirstTerminal.labelled_debt reason id w v history middle performed support pending origin
  dsimp only at result
  let receipt : Terminal.Receipt := ⟨reason,id,⟨(),w,v⟩⟩
  let outcome := Staged.Obligations.Terminal.disposed (history ++ middle).length reason
  let after := settle [ticket] outcome ledger
  let debt : CleanupDebt := ⟨ticket,position,ordinal,outcome⟩
  let afterDebts := forgetFreedCell (history ++ middle) generation id (debt :: debts)
  refine ⟨v,middle ++ [.terminalDrop receipt],after,afterDebts,?_,result.2.1,?_,?_,outcome,rfl⟩
  · simpa only [List.append_assoc] using result.1
  · simpa only [List.append_assoc] using result.2.2.1
  · refine ⟨ticket,position,ordinal,generation,value,(history ++ middle).length,receipt,
      origin.append _,?_,?_,rfl,rfl,result.2.2.2.1⟩
    · simp only [←List.append_assoc,List.getElem?_concat_length]
    · exact (FirstTerminal.labelled_cut reason id w v history middle performed).1

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
