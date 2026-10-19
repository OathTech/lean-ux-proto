import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryQuiet
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastPoll

/-! The real shared-journal poll transfers a pending batch into the active
alias list while retaining all earlier encryption identities and ownership. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

theorem poll : PrefixEnsures (Inv active) Safe Journal.poll
    (fun item => Inv (item.toList ++ active)) := by
  intro w h before
  have history := (Quiet.hooks_safe (past := used h)).poll
  obtain ⟨suffix,extension,same,_⟩ := history w h rfl
  change used (runPrefix Journal.poll w h).2 = used h at same
  refine ⟨suffix,extension,?_,?_⟩
  · change (used (runPrefix Journal.poll w h).2).Nodup
    rw [same]
    exact safe before
  · cases result : (runPrefix Journal.poll w h).1 with
    | error stop => trivial
    | ok output =>
      obtain ⟨item,v⟩ := output
      change Native (used (runPrefix Journal.poll w h).2) (item.toList ++ active) v.wg
      rw [same]
      have native := DriverOwnership.product_native Journal.hooks_projects.poll
        (erasesPrefix_lift (liftWG TxRing.pollSource)) w v h result
      rw [liftWG_run] at native
      cases performed : (TxRing.pollSource.run w.wg).run w.ambient with
      | error stop => simp [performed,Except.map] at native
      | ok output =>
        obtain ⟨⟨out,g⟩,a⟩ := output
        simp only [performed,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
        obtain ⟨rfl,rfl⟩ := native
        exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp TxDisposition.LiveFrontier.poll_ready
            w.wg w.ambient out g a before.1.1 performed,
          EncryptionPast.poll before.1.1.2 before.1.2 w.ambient a performed⟩,
          OccurrenceEncrypt.poll before.2 w.ambient a performed⟩

end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
