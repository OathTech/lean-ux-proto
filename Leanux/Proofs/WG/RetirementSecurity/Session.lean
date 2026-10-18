import Leanux.Proofs.WG.RetirementSecurity.SessionTail

/-! Whole original begin-session accounting: a successful front creates the
only new key occurrence, then the native tail transfers it into the slots.
The proof assumes the incoming exact source-slot account and R2 vacancy;
preservation of the global durable-holder projection is still separate. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

theorem session_account (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (w v : WGWorld) (a b : Ambient)
    (aligned : loans.Aligned p) (account : PeerAccount pid p (loans.credits ++ remaining) w)
    (allocation : AllocationInv history w)
    (run : ((beginSession pid).run w).run a = .ok ((true,v),b)) :
    ∃ ctx middle middleAmbient k,
      ((SessionOrigin.front pid).run w).run a = .ok ((some ctx,middle),middleAmbient) ∧
      keyAt middle ctx.slot = some k ∧ k.internalId = w.keypairCounter + 1 ∧
      PeerAccount pid (rotatedPeer (zeroedPeer p) ctx.slot k.iAmTheInitiator)
        ((loans.rotate ⟨ctx.slot,w.keypairCounter + 1⟩ k.iAmTheInitiator p.keypairNext.isSome).credits ++ remaining) v := by
  rw [SessionOrigin.factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨front,middle,middleAmbient,frontRun,tailRun⟩ := run
  cases front with
  | none => simp at tailRun
  | some ctx =>
    have funded := Credits.front_peer_account pid p ctx w middle a middleAmbient account allocation frontRun
    obtain ⟨k,resident,stamp,_⟩ := funded.2.resident
      (allocation := ⟨ctx.slot,w.keypairCounter + 1⟩) (by simp)
    have completed := session_tail_account pid p loans ⟨ctx.slot,w.keypairCounter + 1⟩
      remaining k aligned funded resident middleAmbient b tailRun
    exact ⟨ctx,middle,middleAmbient,k,frontRun,resident,stamp,completed.2⟩

/-- A normal false result is an actual front refusal; it cannot occur after
paying displaced slot references or publishing the new allocation. -/
theorem session_refused_account (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (w v : WGWorld) (a b : Ambient)
    (aligned : loans.Aligned p) (account : PeerAccount pid p (loans.credits ++ remaining) w)
    (allocation : AllocationInv history w)
    (run : ((beginSession pid).run w).run a = .ok ((false,v),b)) :
    v = w ∧ PeerAccount pid p (loans.credits ++ remaining) v := by
  rw [SessionOrigin.factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨front,middle,middleAmbient,frontRun,tailRun⟩ := run
  cases front with
  | none =>
    cases tailRun
    have same := Origins.front_none pid w v a b frontRun
    exact ⟨same,same ▸ account⟩
  | some ctx =>
    have funded := Credits.front_peer_account pid p ctx w middle a middleAmbient account allocation frontRun
    obtain ⟨k,resident,_,_⟩ := funded.2.resident
      (allocation := ⟨ctx.slot,w.keypairCounter + 1⟩) (by simp)
    have completed := session_tail_account pid p loans ⟨ctx.slot,w.keypairCounter + 1⟩
      remaining k aligned funded resident middleAmbient b tailRun
    cases completed.1

end Leanux.Proofs.WG.RetirementSecurity
