import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueCoreFrames

/-! Bind distribution exposes the already existing focused queue cuts without
changing the actual enqueue action, any event position, or a stopped result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

def focused (action : TxDisposition.Obs α) : PrefixM CausalJournal.Event α :=
  focusPrefix CausalJournal.txEvent CausalJournal.txEvent? action

def enqueueFocused (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event Int :=
  (do
    let some p ← focused (before pid items) | pure (-WG.ENOSPC)
    focused (install pid p items)
    focused (after items)) >>= fun ret => focused (offered items ret)

theorem actual_enqueue (pid : PeerId) (items : List SkbId) :
    Admission.actualOps.enqueue pid items = enqueueFocused pid items := by
  rw [actual_factor]
  symm
  apply (CausalFocus.bind CausalJournal.txEvent CausalJournal.txEvent? (fun _ => rfl) ?_ ?_).2
  · apply CausalFocus.bind CausalJournal.txEvent CausalJournal.txEvent? (fun _ => rfl) (CausalFocus.native CausalJournal.txEvent CausalJournal.txEvent? _ (before_appends pid items))
    intro candidate
    cases candidate with
    | none => exact CausalFocus.pure CausalJournal.txEvent CausalJournal.txEvent? _
    | some p =>
      exact CausalFocus.bind CausalJournal.txEvent CausalJournal.txEvent? (fun _ => rfl)
        (CausalFocus.native CausalJournal.txEvent CausalJournal.txEvent? _ (install_appends pid p items))
        (fun _ => CausalFocus.native CausalJournal.txEvent CausalJournal.txEvent? _ (after_appends items))
  · intro ret
    exact CausalFocus.native CausalJournal.txEvent CausalJournal.txEvent? _ (offered_appends items ret)

theorem offered_erases (items : List SkbId) (ret : Int) :
    ErasesPrefix (offered items ret) (pure ret) := by
  intro w history
  unfold offered
  split <;> try split
  all_goals rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
