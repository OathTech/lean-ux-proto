import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketFrontAccounts

/-! The selected original send supplies socket-front points. Native routing
cuts retain the original peer capture, family guard and both receipt origins. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocketFront
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal CompleteCarrier
abbrev History := List CausalJournal.Event

inductive Point (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (w : World) (h : History) :
    World → History → Prop where
  | source (entry : TxSendFront.ReadEntry pid w h) (ipv4 : Bool) (family : SelectedFamily ipv4 entry.peer)
      (point : SocketFront.RootPoint pid packet entry.peer ipv4 (familyWorld ipv4 entry.world) entry.history u middle) :
      Point pid skb packet w h u middle

theorem socket_appends (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : Appends (Completion.socket pid skb packet peer ipv4) := by
  cases ipv4 <;> exact (Appends.focus _ _ _).receiptObserved

theorem Point.remaining (point : Point pid skb packet w h u middle) :
    ∃remaining,runPrefix (CausalJournal.completionOps.send pid skb packet) w h=runPrefix remaining u middle := by
  cases point with
  | source entry ipv4 family point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      refine ⟨TxSocket.outer pid skb packet w
        (SocketFront.resume pid skb packet entry.peer ipv4 (familyWorld ipv4 entry.world) remaining >>=
          fun ret=>FirstTerminal.focused (afterSocket pid packet ret)),?_⟩
      apply (entry.continuation (.selected ipv4) family).trans
      apply TxSendFront.outer_run_equal
      change runPrefix (FirstTerminal.focused (Completion.socket pid skb packet entry.peer ipv4 >>= afterSocket pid packet))
        (familyWorld ipv4 entry.world) entry.history=_
      rw [TxAccounting.focused_bind (socket_appends _ _ _ _ _) (afterSocket_appends _ _)]
      apply Scheduler.bind_run_equal
      exact (SocketFront.resume_source pid skb packet entry.peer ipv4 _ _).trans
        (SocketFront.resume_run_equal continued)

/-- Security: every reached routing/cache/tunnel-front point belongs to the
same selected send and retains its original packet account and continuation. -/
theorem Point.evidence (before : Owned context (.sending (skb::rest)) h ledger debts w)
    (complete : StagedTerminalComplete.Complete h ledger)
    (point : Point context.pid skb packet w h u middle) : TxSocket.Evidence context ledger debts middle u := by
  cases point with
  | source entry ipv4 family point=>
      exact .accounted ledger debts (.refl _) (point.accounted (entry.accounted (.selected ipv4) before complete))

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
      obtain ⟨context,peer,localEq,_,origin,sending,_⟩:=entry.accounted before
      obtain ⟨ledger,debts,settlements,owned,_,complete⟩:=sending
      rw [←peer] at point
      exact ⟨context,peer,localEq,origin,ledger,debts,settlements.step,point.evidence owned complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocketFront
