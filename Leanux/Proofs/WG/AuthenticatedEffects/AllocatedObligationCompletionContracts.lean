import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCursorFrames

/-! Explicit local obligations at the actual completion callbacks. None is
an initialized premise: concrete source proofs must discharge these before
the whole-caller theorem can be used for global conservation. In particular,
each callback must account for its own stopped prefix, including inner socket
results and partial reference repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedDisposal CompletionCuts

def Holds (context : Context) (phase : Phase) (action : PrefixM CausalJournal.Event α) : Prop :=
  Ensures (State context phase) (Stopped context) action (fun _ => State context phase)

/-- The captured read names this same current packet store. Ambient branch
records may advance between capture and send, but packet material may not. -/
def PacketAt (skb : SkbId) (receipt : RunWitness DataPacket) (w : World) : Prop :=
  receipt.Valid (liftWG (getTxSkb skb)) ∧ receipt.after.wg = w.wg ∧
    TxDisposition.txPackets w.wg skb = some receipt.value

theorem PacketAt.sameWG (before : PacketAt skb receipt w) (same : v.wg = w.wg) :
    PacketAt skb receipt v := by simpa only [PacketAt,same] using before

structure Callbacks (context : Context) (key : KeypairId) : Prop where
  marker : Holds context (.sending context.items)
    (CausalJournal.completionOps.completion context.pid context.items)
  traversal : Holds context (.sending context.items) (CausalJournal.completionOps.traversal context.pid)
  authenticated : Holds context (.sending context.items) (CausalJournal.completionOps.sent context.pid)
  packet : ∀ skb remaining,
    Ensures (State context (.sending (skb :: remaining))) (Stopped context)
      (captureObserved (CausalJournal.completionOps.packet skb))
      (fun receipt h w => State context (.sending (skb :: remaining)) h w ∧
        PacketAt skb receipt w)
  send : ∀ skb remaining receipt,
    Ensures (fun h w => State context (.sending (skb :: remaining)) h w ∧
        PacketAt skb receipt w) (Stopped context)
      (CausalJournal.completionOps.send context.pid skb receipt)
      (fun _ => State context (.sending remaining))
  dataSent : Holds context (.sending []) (CausalJournal.completionOps.dataSent context.pid)
  fresh : Holds context (.sending []) (CausalJournal.completionOps.fresh context.pid)
  free : ∀ skb remaining,
    Ensures (State context (.freeing (skb :: remaining))) (Stopped context)
      (FirstTerminal.cleanupFree skb) (fun _ => State context (.freeing remaining))
  keyRelease : Holds context (.freeing [])
    ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal).access (keypairPutPrefix (some key) false))
  peerRelease : Holds context (.freeing [])
    ((TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal).release (some context.pid))

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
