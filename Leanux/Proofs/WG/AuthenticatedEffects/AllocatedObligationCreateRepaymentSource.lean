import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateTailSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseFrontier

/-! The refusal key repayment ends before the nested peer release. Keeping
this native boundary separate exposes the final staged disposal on both
normal and stopped source paths. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

def keyRepayment (first : SkbId) : PrefixM CausalJournal.Event Unit := do
  let packet ← Admission.actualOps.access (getTxSkbPrefix first)
  Admission.actualOps.access (keypairPutPrefix (some packet.keypair) false)

theorem beforeFree_release_factor (pid : PeerId) (first : SkbId) (ret : Int) :
    beforeFree pid first ret = (do
      if ← Admission.actualOps.step (branch .createDataOk (ret == 0)) then return false
      if ← Admission.actualOps.step (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return false
      keyRepayment first
      Admission.actualOps.release (some pid)
      return true) := by
  simp only [beforeFree,keyRepayment,bind_assoc]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
