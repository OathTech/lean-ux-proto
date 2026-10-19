import Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournalFrames

/-! The transmission hook derives byte readiness at its real socket reads.
Native encryption changes the readiness carrier without adding socket events. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity

theorem transmit (pid : PeerId) : PrefixPreserves (Inv active) Safe (Journal.transmit pid) := by
  have focused := PrefixEnsures.focus Journal.completionEvent Journal.completion?
    (fun e => by cases e <;> rfl) (ReadySocket.step_good pid)
  intro w h before
  have input : ReadySocket.Inv ReadyCiphertext.Inv (h.filterMap Journal.completion?) w :=
    ⟨before.1.2, (safe_eq h) ▸ before.2⟩
  obtain ⟨suffix,extension,good,_⟩ := focused w h input
  have safe : Safe (runPrefix (Journal.transmit pid) w h).2 :=
    (safe_eq _) ▸ good
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (Journal.transmit pid) w h).1 with
  | error stop => trivial
  | ok out =>
    have erased := focusPrefix_erases Journal.completionEvent Journal.completion? (Completion.step_erases pid)
    have native := HolderPoll.native_receipt ((erased w h).symm.trans result)
    exact ⟨(hoare_iff_run_ambient _ _ _).mp (ReadyCiphertext.Tx.step pid)
      w.wg _ out.1 out.2.wg _ before.1 native,safe⟩

theorem iteration : PrefixPreserves (Inv active) Safe (Driver.encryptIterObserved Journal.hooks) := by
  apply product_checked
  · intro past
    exact (show Driver.encryptIterObserved Quiet.nontransmitHooks = Driver.encryptIterObserved Journal.hooks from rfl) ▸
      Driver.encryptIter_history Quiet.hooks_safe.actors
  · intro w h result v before run
    have projected := Driver.encryptIter_projects Journal.hooks_projects
    rw [Driver.nonce_encryptIterObserved_eq] at projected
    exact (hoare_iff_run _ _ _).mp ReadyCiphertext.Encrypt.iteration w result v before
      (DriverOwnership.product_native projected Nonce.encryptIterObserved_erases w v h run)

end Leanux.Proofs.WG.RetirementSecurity.ReadySocketJournal
