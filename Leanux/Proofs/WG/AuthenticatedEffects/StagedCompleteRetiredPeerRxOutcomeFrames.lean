import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxConsumptionFrames
import Leanux.Proofs.WG.Queues.AdmissionOutcome

/-! The native admission receipt determines the ledger independently of its
credit proof. Uniqueness joins that same receipt to the exact holder account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem ExactConsumption.outcome (hi : ExactConsumption holders cs loans msg src ds w v a b r) :
    ∃ next, AdmissionOutcome.Outcome cs next msg src ds w v a b r ∧ Account holders next loans v := by
  obtain ⟨before,ambient,valid,rest⟩ := hi
  cases value:r.value with
  | none =>
    simp only [value] at rest
    exact ⟨cs,⟨before,ambient,valid,by simp only [value]; exact ⟨rest.1,rest.2.1,True.intro⟩⟩,rest.2.2⟩
  | some ctx =>
    simp only [value] at rest
    obtain ⟨owner,funded,stable,slot,_,_,ret,middle,clock,enqueue,finish,choices,endpoint⟩ := rest
    let c : RxCredits.Carrier := ⟨⟨owner.epoch,ctx.slot⟩,owner,.unpublished⟩
    have selected : AdmissionOutcome.carrier r.after ctx=some c :=
      AdmissionOutcome.carrier_at ctx owner funded.funded.carriers slot
    refine ⟨if ret = -ENOSPC then cs else enqueued c::cs,
      ⟨before,ambient,valid,?_⟩,?_⟩
    · simp only [value]
      exact ⟨c,ret,middle,clock,selected,enqueue,finish,choices,rfl⟩
    · by_cases full : ret = -ENOSPC
      · simp only [full,ite_true] at endpoint ⊢
        exact endpoint.1
      · simpa only [full,ite_false] using endpoint

theorem Account.consume_outcome (account : Account holders cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w) (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a=.ok (((),v),b)) :
    ∃ r next, AdmissionOutcome.Outcome cs next msg src ds w v a b r ∧ Account holders next loans v := by
  obtain ⟨r,receipt⟩ := account.consume_data fresh physical a b run
  obtain ⟨next,outcome,after⟩ := receipt.outcome
  exact ⟨r,next,outcome,after⟩

theorem Account.restore_outcome (account : Account holders cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (outcome : AdmissionOutcome.Outcome cs next msg src ds w v a b r) : Account holders next loans v := by
  obtain ⟨actual,derived,other,after⟩ := account.consume_outcome fresh physical a b (AdmissionOutcome.source outcome)
  exact (AdmissionOutcome.unique outcome other).2 ▸ after

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
