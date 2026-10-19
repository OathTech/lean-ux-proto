import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAdmissionQueueCuts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateFrames

/-! Original head-state publication split at its existing published event.
The source borrows the actual key owner, checks its queue, writes the head,
then selects a CPU and schedules work before repaying the borrow. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal

def publicationMark (pid : PeerId) (first : SkbId) (state : PacketState) : PrefixM CausalJournal.Event Unit := do
  if !((← Admission.actualOps.access (getPeerMixed pid)).txQueue.all.any (·.head? == some first)) then
    Admission.actualOps.step (invariant "an item for the tx worker that is not on its peer's tx_queue")
  Admission.actualOps.access (setTxSkbPrefix first fun p => {p with state})
  Admission.actualOps.event (.published pid first state)

def publicationMarkNative (pid : PeerId) (first : SkbId) (state : PacketState) : WG.M Unit := do
  if !((← getPeer pid).txQueue.all.any (·.head? == some first)) then
    invariant "an item for the tx worker that is not on its peer's tx_queue"
  setTxSkb first fun p => {p with state}
  return ()

def publicationSchedule (pid : PeerId) : PrefixM CausalJournal.Event Unit := do
  _ ← Admission.actualOps.access (cpumaskChooseOnlinePrefix pid)
  if !(← Admission.actualOps.step getDev).txWorkQueue.contains pid ||
      (← Admission.actualOps.step (peekQueuedUnit .txWorker pid)) then
    Admission.actualOps.step (recordQueued .txWorker pid)
    Admission.actualOps.step (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})

def publishedPrefix (items : List SkbId) (state : PacketState) : PrefixM CausalJournal.Event (SkbId × PeerId) := do
  let (first,pid) ← Publication.borrow items
  publicationMark pid first state
  return (first,pid)

theorem publication_middle_factor (pid : PeerId) (first : SkbId) (state : PacketState) :
    Publication.middle pid first state = (publicationMark pid first state >>= fun _ => publicationSchedule pid) := by
  simp only [Publication.middle,publicationMark,publicationSchedule,bind_assoc,TxDisposition.bind_ite]

/-- This is the original head publication prefix and its original scheduling
and repayment tail. Event positions and Stop behavior are unchanged. -/
theorem published_prefix_factor (items : List SkbId) (state : PacketState) :
    TxSource.publish Admission.actualOps items state = (do
      let (_,pid) ← publishedPrefix items state
      publicationSchedule pid
      Admission.actualOps.release (some pid)) := by
  rw [Publication.factor]
  simp only [publishedPrefix,publication_middle_factor,bind_assoc,pure_bind]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
