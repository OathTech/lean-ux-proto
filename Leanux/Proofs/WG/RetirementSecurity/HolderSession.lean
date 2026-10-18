import Leanux.Proofs.WG.RetirementSecurity.HolderEntry
import Leanux.Proofs.WG.RetirementSecurity.Session

/-! Whole native session and clear reference equations with entry funding
extracted from actual holders. These endpoints have not yet been reassembled
into the post-state durable projection, so they do not claim initialized
holder-account closure. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem HolderAccount.clear_funded (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) :
    ∃ slots : SlotLoans, ∃ remaining : Credits.Ledger,
      slots.Aligned p ∧ PeerAccount pid p (slots.credits ++ remaining) w ∧
      PeerAccount pid {p with keypairNext := none, keypairPrevious := none, keypairCurrent := none} remaining v := by
  obtain ⟨slots,remaining,aligned,funded⟩ := account.peer_funding found
  exact ⟨slots,remaining,aligned,funded,
    (hoare_iff_run_ambient _ _ _).mp (clear_slot_account pid p slots remaining aligned)
      w a () v b funded run⟩

theorem HolderAccount.session_funded (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (allocation : Lifetimes.AllocationInv history w)
    (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((true,v),b)) :
    ∃ slots : SlotLoans, ∃ remaining : Credits.Ledger,
      slots.Aligned p ∧ PeerAccount pid p (slots.credits ++ remaining) w ∧
      ∃ ctx middle middleAmbient k,
        ((SessionOrigin.front pid).run w).run a = .ok ((some ctx,middle),middleAmbient) ∧
        keyAt middle ctx.slot = some k ∧ k.internalId = w.keypairCounter + 1 ∧
        PeerAccount pid (rotatedPeer (zeroedPeer p) ctx.slot k.iAmTheInitiator)
          ((slots.rotate ⟨ctx.slot,w.keypairCounter + 1⟩ k.iAmTheInitiator
            p.keypairNext.isSome).credits ++ remaining) v := by
  obtain ⟨slots,remaining,aligned,funded⟩ := account.peer_funding found
  exact ⟨slots,remaining,aligned,funded,
    session_account pid p slots remaining w v a b aligned funded allocation run⟩

end Leanux.Proofs.WG.RetirementSecurity
