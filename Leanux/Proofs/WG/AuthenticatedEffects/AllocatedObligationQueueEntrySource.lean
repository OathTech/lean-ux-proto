import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueHandoffContracts

/-! Original mark/read/full-guard prefix before peer-queue installation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def beforeNative (pid : PeerId) (items : List SkbId) : WG.M (Option Peer) := do
  let some first := items.head? | invariant "an empty ring item"
  setTxSkb first fun p => {p with state := .uncrypted}
  let p ← getPeer pid
  if ← branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS) then return none
  return some p

theorem before_erases (pid : PeerId) (items : List SkbId) :
    ErasesPrefix (before pid items) (liftWG (beforeNative pid items)) := by
  unfold before beforeNative
  cases head : items.head? <;> simp only [liftWG_bind,liftWG_pure,apply_ite]
  · exact erasesPrefix_lift _
  · apply erasesPrefix_bind (TxDisposition.nativeAccess_erases (setTxSkbPrefix_erases _ _))
    intro _
    apply erasesPrefix_bind (TxDisposition.nativeAccess_erases (getPeerMixed_erases _))
    intro peer
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro full
    cases full <;> exact erasesPrefix_pure _

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
