import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxAccountingFrames

/-! The actual inner socket receipt supplies byte-accounting entry. Its
continuation retains the outer receipt captured at the original send entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxPostSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal SocketInterior CompleteCarrier
abbrev History := List CausalJournal.Event

inductive Point (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (w : World) (h : History) :
    World → History → Prop where
  | accounting (entry : TxSocket.Entry pid packet w h)
      (point : TxAccounting.Point pid packet (resultCode entry.result) (resultWorld entry.frontWorld entry.result)
        (entry.history++[.old (.socket (entry.socket skb))]) u middle) : Point pid skb packet w h u middle

theorem Point.remaining (point : Point pid skb packet w h u middle) :
    ∃remaining,runPrefix (CausalJournal.completionOps.send pid skb packet) w h=runPrefix remaining u middle := by
  cases point with
  | accounting entry point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      exact ⟨TxSocket.outer pid skb packet w remaining,
        (entry.continuation skb .recorded).trans (TxSendFront.outer_run_equal continued)⟩

/-- Security: native byte accounting starts after the exact packet socket
settlement and carries that same successor ledger to the outer send receipt. -/
theorem Point.evidence
    (before : Owned context (.sending (skb::rest)) h ledger debts w)
    (complete : StagedTerminalComplete.Complete h ledger) (packetAt : PacketAt skb packet w)
    (point : Point context.pid skb packet w h u middle) : TxSocket.Evidence context ledger debts middle u := by
  cases point with
  | accounting entry point=>
      obtain ⟨waiting⟩:=entry.awaiting before complete packetAt
      let support : FirstTerminal.Support _ _ ledger debts _:=
        ⟨waiting.before.entry.core.physical,waiting.before.entry.core.valid⟩
      exact .accounted _ _ (support.settle waiting.pending waiting.outcome).1
        (point.accounted ⟨waiting.after.entry,waiting.afterComplete⟩)

inductive WorkerPoint (pid : PeerId) (w : World) (h : History) : World → History → Prop where
  | send (entry : TxSending.SendEntry pid w h skb packet u middle)
      (point : Point pid skb packet u middle v last) : WorkerPoint pid w h v last

theorem WorkerPoint.remaining (point : WorkerPoint pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | send entry point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      exact ⟨remaining >>= entry.afterSend,entry.continuation.trans (Scheduler.bind_run_equal _ continued)⟩

variable {initial : Staged.Obligations.Ledger}

theorem WorkerPoint.evidence (before : Accounted h initial [] locals w.wg)
    (point : WorkerPoint pid w h u middle) :
    ∃context : Context,context.pid=pid ∧ context.locals=locals ∧ context.initialLedger=initial ∧
      ∃ledger debts,Staged.Obligations.Step initial ledger ∧ TxSocket.Evidence context ledger debts middle u := by
  cases point with
  | send entry point=>
      obtain ⟨context,peer,localEq,_,origin,sending,packetAt⟩:=entry.accounted before
      obtain ⟨ledger,debts,settlements,owned,_,complete⟩:=sending
      rw [←peer] at point
      exact ⟨context,peer,localEq,origin,ledger,debts,settlements.step,point.evidence owned complete packetAt⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxPostSocket
