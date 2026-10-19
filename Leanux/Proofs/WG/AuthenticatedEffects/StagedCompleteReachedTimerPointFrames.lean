import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointSource

/-! Endpoint transport derives from the actual source contracts. This does
not assert a returned world on failure or cover an atomic interior by erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

theorem Native.checked (token : Native) : Checked token.action := by
  cases token with
  | world => exact PrefixEnsures.lift _ Consume.Leaf.carrier_safe (by intro h w value v before run; cases run; exact before)
  | history => exact Consume.Leaf.Native.checked .history
  | selected receipt =>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.old (.timerSelected receipt)) rfl (fun _ => rfl))
  | scope event =>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.scope event) rfl (fun _ => rfl))

theorem Child.checked (token : Child) : Checked token.action := by
  cases token with
  | release peer => exact WorkService.Points.Child.checked (.release peer)
  | flushedSend pid => exact WorkService.Points.Child.checked (.flushedSend pid)
  | keepalive pid => exact CompletePoll.state _ (CompleteProduct.source_state (CompleteTransmit.keepalive pid))
  | purge pid => exact CompletePoll.state _ (CompleteSource.purge pid CompleteProduct.Safe CompleteProduct.account_safe)
  | zero pid => exact Consume.Leaf.native_checked _ (ZeroTimer.frame pid)

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value => exact CompletePoll.pure_checked _ CompleteProduct.account_safe value
  | native token => exact token.checked
  | work source => exact source.checked
  | child token => exact token.checked
  | failed failure next =>
    intro w h before
    obtain ⟨reason,run⟩ := failure.run w h
    exact ⟨[],by simp only [runPrefix_bind,run,List.append_nil],by simpa only [runPrefix_bind,run] using Consume.Leaf.carrier_safe h w before,by simp only [runPrefix_bind,run]⟩
  | bind head tail ihHead ihTail => exact CompletePoll.bind_checked _ ihHead ihTail
  | marked label shape ih => exact ih

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h = (.ok (value,u),middle)) : Carrier middle u := by
  obtain ⟨suffix,extended,safe,kept⟩ := shape.checked w h before
  rw [performed] at kept
  exact kept
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points
