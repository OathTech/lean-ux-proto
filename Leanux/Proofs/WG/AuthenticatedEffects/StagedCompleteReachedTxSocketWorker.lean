import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSocketFrames

/-! Socket intervals are reached from the original worker selection and
ordered send prefix. Their ownership is derived from that same entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompleteCarrier Staged.Obligations
variable {initial : Ledger}

inductive WorkerPoint (pid : PeerId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | socket (entry : TxSending.SendEntry pid w h skb packet u middle)
      (point : Point pid skb packet u middle v last) : WorkerPoint pid w h v last

theorem WorkerPoint.remaining (point : WorkerPoint pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | socket entry point=>
    refine ⟨remainder point >>= entry.afterSend,?_⟩
    rw [entry.continuation,runPrefix_bind,remainder_run point,runPrefix_bind]

noncomputable def workerRemainder (point : WorkerPoint pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem workerRemainder_run (point : WorkerPoint pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (workerRemainder point) u middle :=
  Classical.choose_spec point.remaining

/-- Security: native socket egress and its receipt settle the exact ticket
selected by the original worker. Every cut retains the original ledger
lineage, or its pending socket receipt, before subsequent cleanup. -/
theorem WorkerPoint.evidence (before : Accounted h initial [] locals w.wg)
    (point : WorkerPoint pid w h u middle) :
    ∃context : Context,context.pid=pid ∧ context.locals=locals ∧ context.initialLedger=initial ∧
      ∃ledger debts,Staged.Obligations.Step initial ledger ∧ Evidence context ledger debts middle u := by
  cases point with
  | socket entry point=>
    obtain ⟨context,peer,localEq,_,origin,sending,packetAt⟩:=entry.accounted before
    obtain ⟨ledger,debts,settlements,owned,_,complete⟩:=sending
    rw [←peer] at point
    exact ⟨context,peer,localEq,origin,ledger,debts,settlements.step,point.evidence owned complete packetAt⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
