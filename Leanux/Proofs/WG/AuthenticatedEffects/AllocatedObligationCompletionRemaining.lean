import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionAccounting

/-! The remaining concrete completion obligations, after discharging native
packet capture, the completion marker, traversal and send timers, each ordinary
packet free and key repayment. The remaining source cuts stay explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedDisposal CompletionCuts

structure Remaining (context : Context) : Prop where
  send : ∀ skb rest receipt,
    Ensures (fun h w => State context (.sending (skb :: rest)) h w ∧ PacketAt skb receipt w)
      (Stopped context) (CausalJournal.completionOps.send context.pid skb receipt)
      (fun _ => State context (.sending rest))
  fresh : Holds context (.sending []) (CausalJournal.completionOps.fresh context.pid)
  peerRelease : Holds context (.freeing [])
    ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal).release (some context.pid))

theorem Remaining.callbacks (remaining : Remaining context) : Callbacks context key where
  marker := marker_checked context
  traversal := traversal_checked context _
  authenticated := authenticated_checked context _
  packet := packet_checked context
  send := remaining.send
  dataSent := dataSent_checked context _
  fresh := remaining.fresh
  free := free_checked context
  keyRelease := keyRelease_checked context key _
  peerRelease := remaining.peerRelease

/-- Native reads use the current selected cell, and native frees discharge
its terminal cleanup debt. Only the explicitly listed send/timer/reference
source contracts remain required for whole completion and stopped frontiers. -/
theorem checked (remaining : Remaining context) :
    Ensures (State context (.sending context.items)) (Stopped context)
      (completedAndDisposed context key) (fun _ => State context (.freeing [])) :=
  completedAndDisposed_checked remaining.callbacks

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
