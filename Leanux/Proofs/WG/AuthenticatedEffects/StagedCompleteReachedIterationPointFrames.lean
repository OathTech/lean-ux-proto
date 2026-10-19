import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointSource

/-! Concrete normal-state frames for the finite source atoms. The interiors
of the actual worker callbacks remain explicit; no error post-world is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal
open CompleteProduct

theorem Native.checked (token : Native action) : Checked (liftPrefix action) := by
  cases token with
  | ambient => exact CompleteProduct.ambient _
  | peer pid => exact wg _ (state_store _ (peer_read_store pid))
  | packet skb => exact wg _ (state_store _ (skb_read_store skb))
  | hiddenSite => exact CompleteProduct.ambient _
  | appendWork pid => exact wg _ (append_work pid)
  | eraseWork pid => exact wg _ (erase_work pid)
  | advance enc => exact CompleteProduct.ambient _
  | resched worker => exact product_store _ (condResched_sameKernel worker)
  | branch site yes => exact CompleteProduct.ambient _
  | invariant message => exact CompleteProduct.ambient _
  | stopped reason => exact throw_checked reason

theorem Child.checked (token : Child) : Checked token.action := by
  cases token with
  | poll => exact CompleteProduct.poll
  | softirq => exact CompleteProduct.softirq
  | irqExit => exact CompleteProduct.irq_exit
  | encrypt item => exact CompleteProduct.encrypt item
  | transmit pid => exact CompleteProduct.tx_worker pid
  | prepare => exact CompleteProduct.prepare
  | release pid => exact CompleteProduct.state (CompleteProduct.release (some pid))
  | handshake => exact CompleteProduct.state CompleteProduct.handshake

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value => exact pure_checked value
  | native token => exact token.checked
  | child token => exact token.checked
  | bind head tail ihHead ihTail => exact bind_checked ihHead ihTail
  | marked label shape ih => exact ih

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h = (.ok (value,u),middle)) : Carrier middle u :=
  Scheduler.checked_normal shape.checked before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
