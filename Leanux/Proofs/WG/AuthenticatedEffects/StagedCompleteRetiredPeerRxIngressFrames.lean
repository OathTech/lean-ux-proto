import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxOutcomeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxEncryptFrames
import Leanux.Proofs.WG.Queues.AdmissionCaller

/-! The actual receive front preserves the exact account before its possible
data admission. The existing source outcome fixes the next ledger and the
unchanged receive observer fixes the history occurrence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders CounterWindow

theorem Account.receive_front (account : Account holders cs loans w)
    (run : ((AdmissionReceive.front msg src).run w).run a=.ok ((choice,u),c)) : Account holders cs loans u :=
  account.encrypt_fields (congrArg Prod.fst
    ((ProjectedAction.iff_run_ambient _ _ _).mp (AdmissionReceive.front_view msg src) w a choice u c run))

theorem Account.receive (account : Account holders cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (run : ((wgReceive msg src).run w).run a=.ok (((),v),b)) :
    ∃ next, AdmissionReceive.Outcome cs next msg src w v a b ∧ Account holders next loans v := by
  rw [AdmissionReceive.source_factor] at run
  simp only [StateT.run_bind] at run
  cases hf : ((AdmissionReceive.front msg src).run w).run a with
  | error e => simp [hf] at run
  | ok out =>
    rcases out with ⟨⟨choice,u⟩,c⟩
    have afterFront := account.receive_front hf
    cases choice with
    | none =>
      simp only [hf,except_ok_bind,StateT.run_pure] at run
      obtain ⟨⟨_,rfl⟩,rfl⟩ := run
      exact ⟨cs,⟨none,_,_,hf,rfl,rfl,rfl⟩,afterFront⟩
    | some ds =>
      simp only [hf,except_ok_bind] at run
      obtain ⟨receipt,next,outcome,after⟩ := afterFront.consume_outcome
        (AdmissionReceive.front_packets fresh hf) (AdmissionReceive.front_physical physical hf) c b run
      exact ⟨next,⟨some ds,u,c,hf,receipt,outcome⟩,after⟩

theorem Account.receive_restore (account : Account holders cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (outcome : AdmissionReceive.Outcome cs next msg src w v a b) : Account holders next loans v := by
  obtain ⟨actual,derived,after⟩ := account.receive fresh physical outcome.source
  exact (outcome.unique derived) ▸ after

theorem ExactBoundary.receive (account : ExactBoundary cs loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w)
    (run : ((wgReceive msg src).run w).run a=.ok (((),v),b)) :
    ∃ next, AdmissionReceive.Outcome cs next msg src w v a b ∧ ExactBoundary next loans v := by
  obtain ⟨holders,account⟩ := account
  obtain ⟨next,outcome,after⟩ := account.receive fresh physical run
  exact ⟨next,outcome,holders,after⟩

theorem ExactBoundary.receive_step (account : ExactBoundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) history w.wg)
    (run : runPrefix (AdmissionCaller.receive msg src) w h=(.ok ((),v),k)) :
    ∃ next, AdmissionCaller.Step cs next msg src w v h k ∧ ExactBoundary next loans v.wg := by
  have actual := DecryptIteration.native_normal (AdmissionCaller.receive_erases msg src) run
  obtain ⟨next,outcome,after⟩ := account.receive fresh physical actual
  exact ⟨next,⟨run,outcome⟩,after⟩

theorem ExactBoundary.receive_step_restore (account : ExactBoundary cs loans w.wg) (fresh : Packets.Inv w.wg)
    (physical : NativeRxInv epoch (PtrRing.init n) history w.wg)
    (step : AdmissionCaller.Step cs next msg src w v h k) : ExactBoundary next loans v.wg := by
  obtain ⟨holders,account⟩ := account
  exact ⟨holders,account.receive_restore fresh physical step.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
