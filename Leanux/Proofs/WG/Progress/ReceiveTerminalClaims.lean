import Leanux.Proofs.WG.Progress.ReceiveTerminalSource

/-! Result-sensitive contracts for the original receive operations. Only an
empty-start activation gets an entry-to-exit strict decrease claim. The audit
contract concerns the actual last ended iteration, including a failed stop
read; it makes no claim about preceding packet iterations. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env

theorem original_receive_empty_return (entry : Campaign2.Snapshot) :
    Campaign2.Ensures WG.receiveStep (fun s => s = entry)
      (fun value final => value = false →
        (∃ d, entry.wg.device = some d ∧ d.handshakeQueue.peek = none) ∧
        final.wg = entry.wg ∧ final.ambient.hidden = entry.ambient.hidden) := by
  intro g a value v b initial run returned
  subst entry
  subst value
  obtain ⟨d,device,empty,wg,hiddenEq⟩ := receiveStep_false_cut g v a b run
  refine ⟨⟨d,device,empty⟩,?_,hiddenEq⟩
  rw [wg]
  rfl

theorem original_receive_ended_return (active : Activation)
    (receive : active.worker = .receiveWorker) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (Activation.iter active) (fun s => s = entry)
      (fun value final => value = .ended →
        (∃ d, entry.wg.device = some d ∧ d.handshakeQueue.peek = none) ∧
        final.wg = entry.wg ∧ final.ambient.hidden = entry.ambient.hidden) := by
  intro w value v initial run returned
  subst entry
  subst value
  obtain ⟨d,device,empty,wg,hiddenEq⟩ := receive_iteration_ended_cut active receive w v run
  refine ⟨⟨d,device,empty⟩,?_,hiddenEq⟩
  change (Campaign2.snapshot v.wg v.ambient).wg = (Campaign2.snapshot w.wg w.ambient).wg
  rw [wg]
  rfl

theorem original_empty_receive_activation_decrease (active : Activation)
    (receive : active.worker = .receiveWorker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run active)
      (fun s => s.ambient.hidden = some records ∧
        ∃ d, s.wg.device = some d ∧ d.handshakeQueue.peek = none)
      (fun _ s => StrictTail records s.ambient.hidden) := by
  intro w value final pre run
  rcases pre with ⟨present,d,device,empty⟩
  cases value
  exact receive_empty_activation_strict active receive w final d records device empty present run

theorem original_receive_terminal_records (active : Activation)
    (receive : active.worker = .receiveWorker) :
    Campaign2.Product.Returns (observedActivationExit active) (fun _ => True)
      (fun audit _ => ReceiveTerminal audit ∧ ActivationExitFacts active audit) := by
  intro initial _
  exact ⟨_,initial,rfl,receive_activation_terminal active receive initial,
    activationExitRun_facts active initial⟩

end Leanux.Proofs.WG.Progress.RecordSuffix
