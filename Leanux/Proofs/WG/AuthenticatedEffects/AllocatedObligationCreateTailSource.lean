import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionContracts
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateDisposalLoop

/-! The original create return tests and key/peer repayments precede the
labelled free loop. These factors keep that order and do not replace a stopped
repayment by completed disposal. No final journal event is added. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def beforeFree (pid : PeerId) (first : SkbId) (ret : Int) : PrefixM CausalJournal.Event Bool := do
  if ← Admission.actualOps.step (branch .createDataOk (ret == 0)) then return false
  if ← Admission.actualOps.step (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return false
  Admission.actualOps.access (keypairPutPrefix
    (some (← Admission.actualOps.access (getTxSkbPrefix first)).keypair) false)
  Admission.actualOps.release (some pid)
  return true

def beforeFreeNative (pid : PeerId) (first : SkbId) (ret : Int) : WG.M Bool := do
  if ← branch .createDataOk (ret == 0) then return false
  if ← branch .createDataOkEpipe (ret == -WG.EPIPE) then return false
  keypairPut (some (← getTxSkb first).keypair) false
  peerPut (some pid)
  return true

theorem tail_factor (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int) :
    Admission.tail Admission.actualOps free pid items first ret = (do
      let cleanup ← beforeFree pid first ret
      if cleanup then loop (.createRefused pid ret) items else pure ()) := by
  simp only [Admission.tail,beforeFree,loop,bind_assoc,TxDisposition.bind_ite,pure_bind]
  rfl

/-- The whole actual create callback reaches repayment before any refusal
free. Its earlier admission and every existing event remain in place. -/
theorem create_factor (pid : PeerId) (items : List SkbId) :
    Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items = (do
      let some first := items.head? | Admission.actualOps.step (invariant "an empty ring item")
      let ret ← Admission.actual pid items
      let cleanup ← beforeFree pid first ret
      if cleanup then loop (.createRefused pid ret) items else pure ()) := by
  rw [Admission.final_factor]
  cases items.head? with
  | none => rfl
  | some first =>
    simp only
    congr 1
    funext ret
    exact tail_factor pid items first ret

private theorem release_erases (peer : Option PeerId) :
    ErasesPrefix (Admission.actualOps.release peer) (liftWG (peerPut peer)) := by
  have project := TxSource.release_matching CausalJournal.old?
    CausalJournal.txEvent CausalJournal.txEvent? Journal.Event.disposition Journal.disposition?
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    CausalJournal.Event.stagedDisposal (fun _ => rfl) peer
  have native := focusPrefix_erases Journal.Event.disposition Journal.disposition?
    (TxDisposition.nativeAccess_erases (peerPutMixed_erases peer))
  intro w h
  have same := congrArg Prod.fst (project w h)
  simp only [id_eq,Prod.eta] at same
  change (runPrefix (TxSource.releaseObserved CausalJournal.txEvent CausalJournal.txEvent?
    CausalJournal.Event.stagedDisposal peer) w h).1 = _
  cases result : (runPrefix (TxSource.releaseObserved CausalJournal.txEvent CausalJournal.txEvent?
    CausalJournal.Event.stagedDisposal peer) w h).1 <;>
    simpa only [result,Except.map] using same.symm.trans (native w (h.filterMap CausalJournal.old?))

theorem beforeFree_erases (pid : PeerId) (first : SkbId) (ret : Int) :
    ErasesPrefix (beforeFree pid first ret) (liftWG (beforeFreeNative pid first ret)) := by
  have step {α : Type} (action : WG.M α) :
      ErasesPrefix (Admission.actualOps.step action) (liftWG action) :=
    focusPrefix_erases _ _ (erasesPrefix_lift _)
  have read (skb : SkbId) :
      ErasesPrefix (Admission.actualOps.access (getTxSkbPrefix skb)) (liftWG (getTxSkb skb)) :=
    focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases (getTxSkbPrefix_erases skb))
  have put (kid : Option KeypairId) :
      ErasesPrefix (Admission.actualOps.access (keypairPutPrefix kid false)) (liftWG (keypairPut kid false)) :=
    focusPrefix_erases _ _ (TxDisposition.nativeAccess_erases (keypairPutPrefix_erases kid false))
  unfold beforeFree beforeFreeNative
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  apply erasesPrefix_bind (step _)
  intro accepted
  cases accepted with
  | true => exact erasesPrefix_pure _
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply erasesPrefix_bind (step _)
    intro pipe
    cases pipe with
    | true => exact erasesPrefix_pure _
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      apply erasesPrefix_bind (read first)
      intro packet
      apply erasesPrefix_bind (put (some packet.keypair))
      intro _
      apply erasesPrefix_bind (release_erases (some pid))
      intro _
      exact erasesPrefix_pure _

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
