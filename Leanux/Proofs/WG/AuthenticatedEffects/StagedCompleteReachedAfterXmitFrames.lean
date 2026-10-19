import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAfterXmitSource

/-! The fixed post-transmit guard and drain preserve the projected native
packet account; the actual crypt callback retains its complete source proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal CompletePrefix.Product

theorem front_checked : Checked front := by
  unfold front
  repeat' first
    | prefix_deferred_native
    | prefix_product_step

theorem front_history (w : World) (h : List Event) :
    (runPrefix front w h).2=h := by
  have quiet : HistoryFrame some front := by
    unfold front
    apply HistoryFrame.bind (HistoryFrame.lift _ _)
    intro original
    cases original.dev with
    | none => exact HistoryFrame.pure _ _
    | some device =>
      dsimp only
      split
      · exact HistoryFrame.bind (HistoryFrame.lift _ _) (fun _=>
          HistoryFrame.bind (HistoryFrame.lift _ _) (fun _=>HistoryFrame.pure _ _))
      · exact HistoryFrame.bind (HistoryFrame.lift _ _) (fun _=>HistoryFrame.pure _ _)
  simpa only [List.filterMap_some] using quiet w h

theorem crypt_tail_checked : Checked cryptTail := by
  unfold cryptTail
  apply bind_checked Execution.crypt
  intro _
  repeat' first
    | prefix_deferred_native
    | prefix_product_step

theorem send_prefix_checked : Checked sendPrefix := by
  unfold sendPrefix
  apply bind_checked front_checked
  intro selected
  cases selected with
  | none => exact pure_checked false
  | some crypt =>
    cases crypt with
    | false => exact pure_checked true
    | true => exact bind_checked crypt_tail_checked (fun _=>pure_checked true)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
