import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxSelectionFrames

/-! The exact shared TX observer's queue selection prefix. It retains the
native cached queue representation and all source access events. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedConservation

def peek (pid : PeerId) : PrefixM CausalJournal.Event (Option (List SkbId)) := do
  let (first,queue) ← CausalJournal.completionOps.step ((← CausalJournal.completionOps.peer pid).txQueue.peek)
  CausalJournal.completionOps.modifyPeer pid fun p => {p with txQueue := queue}
  return first

theorem transmit_factor (pid : PeerId) : CausalJournal.transmit pid = (do
    let first ← peek pid
    Terminal.bodyWith CausalJournal.completionOps
      (CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion CausalJournal.completionOps)
      (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop) pid first) := by
  simp only [CausalJournal.transmit,Terminal.stepWith,peek,bind_assoc,pure_bind]

theorem peek_erases (pid : PeerId) : ErasesPrefix (peek pid) (liftWG (txPeekSource pid)) := by
  unfold peek txPeekSource
  simp only [liftWG_bind,liftWG_pure]
  apply erasesPrefix_bind (show ErasesPrefix (CausalJournal.completionOps.peer pid) (liftWG (getPeer pid)) from
    focusPrefix_erases _ _ (Completion.access_erases (getPeerMixed_erases pid)))
  intro p
  apply erasesPrefix_bind (show ErasesPrefix (CausalJournal.completionOps.step p.txQueue.peek)
    (liftWG p.txQueue.peek) from focusPrefix_erases _ _ (erasesPrefix_lift _))
  intro pair
  obtain ⟨first,queue⟩ := pair
  have modified := erasesPrefix_bind (show ErasesPrefix
    (CausalJournal.completionOps.modifyPeer pid fun p => {p with txQueue := queue})
    (liftWG (do let p ← getPeer pid; setPeer pid {p with txQueue := queue})) from
    focusPrefix_erases _ _ (Completion.access_erases (modifyPeerKeysPrefix_erases pid _)))
    (fun _ => erasesPrefix_pure first)
  simpa only [liftWG_bind,bind_assoc] using modified

theorem drop_erases (pid : PeerId) (items : List SkbId) :
    ErasesPrefix (CausalJournal.completionOps.drop pid items) (liftWG (txDropSource pid)) :=
  focusPrefix_erases _ _ (focusPrefix_erases _ _ (TxDisposition.drop_erases pid items))

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
