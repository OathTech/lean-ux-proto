import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationDeadEntryFrames

/-! The actual DEAD worker frees its selected list before cached key and peer
repayment. These factors retain that order and the original terminal receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal HandshakeSecurity.StagedConservation

def repay (pid : PeerId) (key : KeypairId) : PrefixM CausalJournal.Event Bool := do
  Admission.actualOps.access (keypairPutPrefix (some key) false)
  Admission.actualOps.release (some pid)
  return true

theorem dead_factor (pid : PeerId) (items : List SkbId) (head : DataPacket) :
    Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head = (do
        loop (.deadBatch pid head) items
        repay pid head.keypair) := by
  simp only [Terminal.deadObserved,Terminal.disposeWith,loop,repay,Admission.actualOps,
    CreateDisposal.free,bind_assoc,pure_bind]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
