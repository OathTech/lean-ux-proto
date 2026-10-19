import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionKeyRelease

/-! The remaining concrete completion obligations, after discharging native
packet capture, the completion marker, authenticated-send timer deletion,
each ordinary packet free and key repayment. The remaining source cuts stay explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedDisposal CompletionCuts

structure Remaining (context : Context) : Prop where
  traversal : Holds context (.sending context.items) (CausalJournal.completionOps.traversal context.pid)
  send : ∀ skb rest receipt,
    Ensures (fun h w => State context (.sending (skb :: rest)) h w ∧ PacketAt skb receipt w)
      (Stopped context) (CausalJournal.completionOps.send context.pid skb receipt)
      (fun _ => State context (.sending rest))
  dataSent : Holds context (.sending []) (CausalJournal.completionOps.dataSent context.pid)
  fresh : Holds context (.sending []) (CausalJournal.completionOps.fresh context.pid)
  peerRelease : Holds context (.freeing [])
    ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal).release (some context.pid))

theorem Remaining.callbacks (remaining : Remaining context) : Callbacks context key where
  marker := marker_checked context
  traversal := remaining.traversal
  authenticated := authenticated_checked context _
  packet := packet_checked context
  send := remaining.send
  dataSent := remaining.dataSent
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
