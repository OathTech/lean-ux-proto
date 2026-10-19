import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateTailFrames

/-! Composition at the actual repayment cut. A successful entry to the free
loop suffices; no completed createData caller is assumed. Earlier stopped
admission or repayment remains distinct from completed packet disposal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

/-- Once the original return guards and repayments reach the refusal loop,
all selected cells receive actual labelled receipts and immutable terminals.
The native backed batch makes each free total; no free-result premise hides
a missing cell or a later stopped enclosing caller. -/
theorem tail_refused (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int)
    (performed : runPrefix (beforeFree pid first ret) w history = (.ok (true,u),history ++ middle))
    (support : FirstTerminal.Support births history ledger debts w.wg)
    (pending : PendingBatch history ledger items) (unique : items.Nodup) :
    ∃ v suffix after afterDebts,
      runPrefix (Admission.tail Admission.actualOps free pid items first ret) w history =
        (.ok ((),v),history ++ middle ++ suffix) ∧
      Staged.Obligations.Step ledger after ∧
      FirstTerminal.Support births (history ++ middle ++ suffix) after afterDebts v.wg ∧
      AllDropped (history ++ middle ++ suffix) after (.createRefused pid ret) items := by
  have ready := beforeFree_normal pid first ret performed support
  obtain ⟨v,suffix,after,afterDebts,freed,step,kept,dropped⟩ :=
    loop_total (.createRefused pid ret) items unique ready (pending.append middle)
  refine ⟨v,suffix,after,afterDebts,?_,step,kept,dropped⟩
  rw [tail_factor,runPrefix_bind,performed]
  exact freed

/-- The same actual admission and repayment executions compose with the
native refusal frees. The input ledger, native batch and every history
position are shared across the source cuts. -/
theorem create_refused (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int)
    (head : items.head? = some first)
    (admission : runPrefix (Admission.actual pid items) w history = (.ok (ret,u),history ++ admitted))
    (repayment : runPrefix (beforeFree pid first ret) u (history ++ admitted) =
      (.ok (true,z),(history ++ admitted) ++ repaid))
    (entry : Admission.Entry ledger debts locals pid items history w)
    (valid : Valid births ledger) (pending : PendingBatch history ledger items) (unique : items.Nodup) :
    ∃ v suffix after afterDebts,
      runPrefix (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w history =
        (.ok ((),v),((history ++ admitted) ++ repaid) ++ suffix) ∧
      Staged.Obligations.Step ledger after ∧
      FirstTerminal.Support births (((history ++ admitted) ++ repaid) ++ suffix) after afterDebts v.wg ∧
      AllDropped (((history ++ admitted) ++ repaid) ++ suffix) after (.createRefused pid ret) items := by
  obtain ⟨_,_,_,normal⟩ := Admission.actual_contract ledger debts locals pid items w history entry
  rw [admission] at normal
  have support : FirstTerminal.Support births (history ++ admitted) ledger debts u.wg := ⟨normal.1,valid⟩
  obtain ⟨v,suffix,after,afterDebts,finished,step,kept,dropped⟩ :=
    tail_refused pid items first ret repayment support (pending.append admitted) unique
  refine ⟨v,suffix,after,afterDebts,?_,step,kept,dropped⟩
  rw [Admission.final_factor,head]
  simp only
  rw [runPrefix_bind,admission]
  exact finished

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
