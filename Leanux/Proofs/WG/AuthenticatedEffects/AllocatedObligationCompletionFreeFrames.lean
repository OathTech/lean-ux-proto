import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCapture

/-! One exact native free advances the selected ownership cursor by one.
This is separate from terminal settlement: ordinary cleanup retains the
already chosen outcome and removes only its physical debt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CompletionCuts

theorem native_free_total (resident : TxDisposition.txPackets w.wg skb = some packet) :
    ∃ v, (liftWG (freeTxSkb skb)).run w = .ok ((),v) := by
  cases device : w.wg.dev with
  | none => simp [TxDisposition.txPackets,device] at resident
  | some d =>
    have cell : d.txSkbs[skb]? = some packet := by simpa [TxDisposition.txPackets,device] using resident
    refine ⟨{w with wg := Packets.update w.wg (fun d => {d with txSkbs := d.txSkbs.erase skb})},?_⟩
    rw [liftWG_run,Packets.freeTxSkb_run _ _ d skb packet device cell]
    rfl

theorem free_ownership
    (coverage : TxCoverage (⟨.selected,pid,skb :: remaining⟩ :: locals) w.wg)
    (inventory : TxInventory (⟨.selected,pid,skb :: remaining⟩ :: locals) w.wg)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    TxCoverage (⟨.selected,pid,remaining⟩ :: locals) v.wg ∧
      TxInventory (⟨.selected,pid,remaining⟩ :: locals) v.wg := by
  have splitCoverage : TxCoverage (⟨.selected,pid,[skb]⟩ :: ⟨.selected,pid,remaining⟩ :: locals) w.wg := coverage
  have splitInventory : TxInventory (⟨.selected,pid,[skb]⟩ :: ⟨.selected,pid,remaining⟩ :: locals) w.wg :=
    ⟨inventory.localUnique,inventory.queueUnique,inventory.peersSeparate,
      inventory.localsSeparate,inventory.localResident,inventory.queueResident⟩
  rw [liftWG_run] at run
  cases native : ((freeTxSkb skb).run w.wg).run w.ambient with
  | error reason => simp [native,Except.map] at run
  | ok out =>
    rcases out with ⟨⟨value,after⟩,ambient⟩
    cases value
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    have same := congrArg World.wg run.2
    have singleton : ((TxDisposition.freeList [skb]).run w.wg).run w.ambient =
        .ok (((),after),ambient) := by
      simpa [TxDisposition.freeList,List.forIn_cons,List.forIn_nil,bind_assoc] using native
    exact same ▸ ⟨splitCoverage.free_batch _ _ singleton,(splitInventory.free_batch _ _ singleton).1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
