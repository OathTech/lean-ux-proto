import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTxHistory
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTxNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct

/-! Product callback for the actual TX source. Stopped paths retain the
worker's actual saved accounting cut, with its original intermediate debts
and locals. Native allocation is paired on that same execution. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open AllocatedObligation.CompletionBatch.Converse

private theorem tx_accounted (pid : PeerId) :
    PrefixPreserves (fun h w => CompleteCarrier.Carrier [] [] h w.wg w.ambient)
      Safe (CausalJournal.transmit pid) := by
  intro w h before
  obtain ⟨ledger,entry⟩ := before
  obtain ⟨suffix,grown⟩ := TxHistory.transmit pid w h
  have checked := Worker.transmit_checked pid entry
  refine ⟨suffix,grown,?_⟩
  cases performed : runPrefix (CausalJournal.transmit pid) w h with
  | mk outcome last =>
    rw [performed] at checked
    cases outcome with
    | error reason =>
      obtain ⟨after,debts,locals,cut,_,accounted⟩ := checked.2
      exact ⟨⟨debts,.accounted after locals last cut accounted⟩,True.intro⟩
    | ok out =>
      obtain ⟨after,_,accounted⟩ := checked.entry
      exact ⟨account_safe after last out.2.wg accounted,⟨after,accounted⟩⟩

theorem tx_worker (pid : PeerId) : Checked (CausalJournal.hooks.transmit pid) :=
  pair_product (tx_accounted pid) (TxNative.erases pid) (TxNative.allocated_product pid)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
