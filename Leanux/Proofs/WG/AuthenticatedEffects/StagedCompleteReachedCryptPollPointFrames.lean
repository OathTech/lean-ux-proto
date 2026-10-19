import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCryptPollPointSource

/-! Polling changes the ring alias but preserves the authoritative staged and
TX owners. Both receipts extend the same ledger without a birth or terminal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal CompleteCarrier
open Staged.Obligations

theorem native_accounted (body : WG.M α) (frame : SameView StagedEntry.view body)
    (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (liftPrefix (liftWG body)) w h = (.ok (value,u),middle)) :
    Accounted middle ledger debts locals u.wg := by
  simp only [runPrefix_lift] at performed
  have history := congrArg Prod.snd performed
  cases history
  exact before.same_view ((ProjectedAction.iff_run _ _ _).mp
    (sameView_liftWG (fun w : World => StagedEntry.view w.wg) StagedEntry.view body frame
      (fun _ _ _ same => same)) w value u (congrArg Prod.fst performed))

theorem emit_accounted {w u : World} (event : Event) (birth : birthPackets event = [])
    (terminal : StagedTerminalComplete.Quiet event)
    (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix (emitPrefix event) w h = (.ok (value,u),middle)) :
    Accounted middle ledger debts locals u.wg := by
  simp only [runPrefix_emit] at performed
  cases performed
  exact before.append_quiet [event] (by simpa using birth) (by simpa using terminal)

theorem Native.accounted (token : Native) {value : token.Result}
    (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix token.action w h = (.ok (value,u),middle)) :
    Accounted middle ledger debts locals u.wg := by
  cases token with
  | world => cases performed; exact before
  | device => exact native_accounted _ (TimerFrames.store getDev_sameWGStore) before performed
  | install ring => exact native_accounted _ (ReceiveFrames.device (fun d => {d with encryptQueue := ring})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) before performed
  | polled item => exact emit_accounted _ rfl (fun _ => rfl) before performed
  | receipt value => exact emit_accounted _ rfl (fun _ => rfl) before performed

theorem Shape.accounted {action : PrefixM Event α} (shape : Shape action) {value : α}
    (before : Accounted h ledger debts locals w.wg)
    (performed : runPrefix action w h = (.ok (value,u),middle)) :
    Accounted middle ledger debts locals u.wg := by
  induction shape generalizing w h u middle with
  | pure value => cases performed; exact before
  | native token => exact token.accounted before performed
  | bind head tail ihHead ihTail =>
      rename_i body next
      rw [runPrefix_bind] at performed
      cases leading : runPrefix body w h with
      | mk result after =>
        cases result with
        | error reason => simp only [leading] at performed; cases performed
        | ok pair =>
          obtain ⟨selected,v⟩ := pair
          simp only [leading] at performed
          exact ihTail selected (ihHead before leading) performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CryptPoll.Points
