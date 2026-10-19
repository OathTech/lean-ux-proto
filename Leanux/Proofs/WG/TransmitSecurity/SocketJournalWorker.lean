import Leanux.Proofs.WG.TransmitSecurity.SocketJournalFrames

/-! Native TX completion connects its selected coherent batch to every socket
receipt. Its rescheduling suffix preserves that history through later Stop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.SocketJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

theorem hook (pid : PeerId) : PrefixPreserves (Inv active) Safe (Journal.transmit pid) := by
  have focused := (CompletionPeer.step pid).focus Journal.completionEvent Journal.completion?
    (fun e => by cases e <;> rfl)
  intro w h before
  have old : CompletionPeer.Good (h.filterMap Journal.completion?) := (safe_eq h) ▸ before.2
  obtain ⟨suffix,extension,good,_⟩ := focused w h ⟨before.1.2,old⟩
  have safe : Safe (runPrefix (Journal.transmit pid) w h).2 := (safe_eq _).symm ▸ good
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix (Journal.transmit pid) w h).1 with
  | error stop => trivial
  | ok out =>
    have erased : ErasesPrefix (Journal.transmit pid) (liftWG (txStep pid)) :=
      focusPrefix_erases _ _ (Completion.step_erases pid)
    exact ⟨(hoare_iff_run _ _ _).mp
      (PublicationPoll.native_product _ _ (BatchCoherence.Tx.step pid))
      w out.1 out.2 before.1 ((erased w h).symm.trans result),safe⟩

private theorem lift_closed (action : Leanux.M α)
    (frame : Preserves (fun w : World => BatchCoherence.Native.Coherent [] active w.wg) action) :
    PrefixPreserves (Inv active) Safe (liftPrefix action) := by
  apply PrefixEnsures.lift
  · intro _ _ before; exact before.2
  · intro h w value v before run
    exact ⟨(hoare_iff_run _ _ _).mp frame w value v before.1 run,before.2⟩

private theorem resched : PrefixPreserves (Inv active) Safe
    (Driver.reschedObserved .txWorker .txNeedResched) := by
  unfold Driver.reschedObserved
  apply PrefixPreserves.bind (lift_closed _ (BatchCoherence.Decrypt.product_store (condResched_sameKernel _)))
  intro yes
  exact lift_closed _ (productAmbient_spec _ _ (fun _ _ before => before))

theorem tx_iteration (pid : PeerId) :
    PrefixPreserves (Inv []) Safe (Driver.txIterObserved Journal.hooks pid) := by
  unfold Driver.txIterObserved workerIterPrefix
  apply PrefixPreserves.bind (hook pid)
  intro more
  split
  · exact PrefixPreserves.pure (fun _ _ before => before.2) _
  · apply PrefixPreserves.bind resched
    intro yes
    exact PrefixPreserves.pure (fun _ _ before => before.2) _

end Leanux.Proofs.WG.TransmitSecurity.SocketJournal
