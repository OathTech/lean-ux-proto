import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateRepaymentFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateTailFrames

/-! The actual successful repayment reaches the refusal loop with its own
successor ledger. Final peer disposal may have changed staged obligations;
the same allocated batch and all prior terminals survive into native frees.
Full queue/entry transport through that free loop remains a separate result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
set_option pp.structureInstances false

/-- The actual refusal tail frees every backed batch cell after the original
key/peer repayments, including final peer disposal. The source cut's complete
owned successor is retained explicitly; terminal settlement then preserves
physical backing and the first named result for every selected packet. -/
theorem tail_from_owned (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int)
    (performed : runPrefix (beforeFree pid first ret) w history = (.ok (true,u),middle))
    (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg)
    (pending : PendingBatch history ledger items) (unique : items.Nodup) :
    ∃ releaseLedger v suffix after afterDebts,
      Staged.Obligations.Step ledger releaseLedger ∧
      Owned releaseLedger debts locals middle u ∧ Packets.Inv u.wg ∧
      runPrefix (Admission.tail Admission.actualOps free pid items first ret) w history =
        (.ok ((),v),middle ++ suffix) ∧
      Staged.Obligations.Step releaseLedger after ∧
      FirstTerminal.Support (births middle) (middle ++ suffix) after afterDebts v.wg ∧
      AllDropped (middle ++ suffix) after (.createRefused pid ret) items := by
  have result := beforeFree_cases pid first ret owned bounded
  rw [performed] at result
  obtain ⟨releaseLedger,step,frame,_,atLoop,bounds⟩ := result
  obtain ⟨repaid,extended⟩ := beforeFree_appends pid first ret w history
  rw [performed] at extended
  change middle = history ++ repaid at extended
  have batch : PendingBatch middle releaseLedger items := by
    rw [extended]
    exact (pending.allocated_frame frame).append repaid
  have support : FirstTerminal.Support (births middle) middle releaseLedger debts u.wg :=
    ⟨atLoop.1.physical,atLoop.1.valid⟩
  obtain ⟨v,suffix,after,afterDebts,freed,steps,kept,dropped⟩ :=
    loop_total (.createRefused pid ret) items unique support batch
  refine ⟨releaseLedger,v,suffix,after,afterDebts,step,atLoop,bounds,?_,steps,kept,dropped⟩
  rw [tail_factor,runPrefix_bind,performed]
  exact freed

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
