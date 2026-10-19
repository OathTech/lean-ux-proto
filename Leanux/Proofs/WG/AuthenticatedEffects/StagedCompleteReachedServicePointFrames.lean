import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointSource

/-! Concrete projection frames at actual service native boundaries. All
normal child frames come from the same original source run; no invented
error state or delete-entry promotion is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal
open CompleteProduct

theorem NativeKind.checked (kind : NativeKind) : Checked kind.action := by
  cases kind with
  | wg => exact wg_read
  | device => exact CompleteProduct.wg _ (state_store _ getDev_sameWGStore)
  | env => exact env_read
  | routing => exact CompleteProduct.routing _
  | ambient body => exact CompleteProduct.ambient body
  | ambientEdit f => exact CompleteProduct.ambient _
  | envEdit f => exact env_edit f
  | reset => exact wg_bookkeeping _ (fun _=>rfl)
  | sentClear => exact wg_bookkeeping _ (fun _=>rfl)
  | pass value => exact wg_bookkeeping _ (fun _=>rfl)
  | jiffies value => exact wg_bookkeeping _ (fun _=>rfl)
  | delete pid timer => exact CompleteProduct.wg _ (delete_timer pid timer)
  | peek => exact product_store _ peekNextSite_sameKernel
  | timerWorker timer => exact product_store _ (timerWorker_sameKernel timer)
  | stepComplete expiry => exact product_store _ (TransmitSecurity.Nonce.Frames.step_complete expiry)
  | nothingDue expiry => exact product_store _ (TransmitSecurity.Nonce.Frames.nothing_due expiry)
  | delivery sent => exact emit _ rfl (fun _=>rfl)

theorem Native.checked (token : Native action) : Checked action := by
  cases token with
  | kind source => exact source.checked

theorem Family.checked (family : Family) : Checked family.action := by
  cases family with
  | schedule stack => exact Execution.scheduled stack
  | sends => exact Execution.sends
  | sendWorker => exact scheduled_send
  | clearWorker => exact scheduled_clear
  | timer pid timer => exact state (CompleteProduct.timer pid timer)
  | selected device bound pid timer entry => exact timer_selected device bound pid timer entry
  | finished token => exact timer_finished token

theorem Child.checked (token : Child action) : Checked action := by
  cases token with
  | family source => exact source.checked

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value => exact pure_checked value
  | native token => exact token.checked
  | child token => exact token.checked
  | bind head tail ihHead ihTail => exact bind_checked ihHead ihTail
  | marked label shape ih => exact ih

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h = (.ok (value,u),middle)) : Carrier middle u :=
by
  obtain ⟨_,_,_,post⟩ := shape.checked w h before
  simpa only [performed] using post

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
