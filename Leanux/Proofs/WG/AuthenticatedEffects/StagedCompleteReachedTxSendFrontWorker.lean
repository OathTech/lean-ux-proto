import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSendFrontFrames

/-! Send-front points retain the original worker selection, send-list cursor
and captured packet. Their source remainders do not assume a packet account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSendFront
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompleteCarrier Staged.Obligations
variable {initial : Ledger}

inductive WorkerPoint (pid : PeerId) (w : World) (h : History) : World → History → Prop where
  | send (entry : TxSending.SendEntry pid w h skb packet u middle)
      (point : Point pid skb packet u middle v last) : WorkerPoint pid w h v last

theorem WorkerPoint.remaining (point : WorkerPoint pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | send entry point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      exact ⟨remaining >>= entry.afterSend,entry.continuation.trans (Scheduler.bind_run_equal _ continued)⟩

/-- Security: every declared send-front and completed-send cut belongs to
the same initialized worker lineage, including unsupported endpoint families. -/
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

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSendFront
