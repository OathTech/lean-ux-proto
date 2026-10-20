import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSelectionSource

/-! The original read/dequeue cuts derive their own account from entry.
Selected ownership is kept distinct from idle ownership and retains the
actual pending batch. Send/disposal interiors are not covered by this file. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSelector
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CompleteCarrier AllocatedObligation CompletionBatch

def ReadEntry (pid : PeerId) (result : Option (List SkbId × DataPacket))
    (h : List CausalJournal.Event) (ledger : Ledger) (locals : List TxLocalBatch) (w : World) : Prop :=
  Accounted h ledger [] locals w.wg ∧ ∀items head,result=some (items,head) →
    ∀p,peerAt w.wg pid=some p → p.txQueue.peeked=some items

theorem read_body_entry (before : Accounted h ledger [] locals w.wg)
    (cached : ∀p,peerAt w.wg pid=some p → p.txQueue.peeked=first)
    (performed : runPrefix (readBody first) w h=(.ok (result,v),last)) :
    ReadEntry pid result last ledger locals v := by
  unfold readBody at performed
  rw [runPrefix_bind] at performed
  cases readied : runPrefix (TxWorker.ready first) w h with
  | mk outcome middle=>
    rw [readied] at performed
    cases outcome with
    | error reason=>cases performed
    | ok pair=>
      obtain ⟨go,u⟩:=pair
      obtain ⟨atReady,sameReady,shape⟩:=ready before readied
      cases go with
      | false=>
        simp only [Bool.not_false,ite_true,runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at performed
        obtain ⟨⟨rfl,rfl⟩,rfl⟩:=performed
        exact ⟨atReady,by intro items head impossible;cases impossible⟩
      | true=>
        obtain ⟨items,id,_,chosen,nonempty,_,_⟩:=shape rfl
        simp only [Bool.not_true,Bool.false_eq_true,ite_false,chosen,nonempty] at performed
        rw [runPrefix_bind] at performed
        cases read : runPrefix (CausalJournal.completionOps.packet id) u middle with
        | mk outcome after=>
          rw [read] at performed
          cases outcome with
          | error reason=>cases performed
          | ok pair=>
            obtain ⟨head,q⟩:=pair
            obtain ⟨atRead,sameRead⟩:=packet atReady read
            simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at performed
            obtain ⟨⟨rfl,rfl⟩,rfl⟩:=performed
            refine ⟨atRead,?_⟩
            intro other packet equal p found
            obtain ⟨rfl,rfl⟩:=Option.some.inj equal
            rw [sameRead,sameReady] at found
            exact (cached p found).trans chosen

theorem read_entry (before : Accounted h ledger [] locals w.wg)
    (performed : runPrefix (workerReadPrefix pid) w h=(.ok (result,v),last)) :
    ReadEntry pid result last ledger locals v := by
  change runPrefix (TxSelection.peek pid >>= readBody) w h=_ at performed
  rw [runPrefix_bind] at performed
  cases peeked : runPrefix (TxSelection.peek pid) w h with
  | mk outcome middle=>
    rw [peeked] at performed
    cases outcome with
    | error reason=>cases performed
    | ok pair=>
      obtain ⟨first,u⟩:=pair
      obtain ⟨atPeek,cached⟩:=peek before peeked
      exact read_body_entry atPeek cached performed

inductive Evidence (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (h : List CausalJournal.Event) (w : World) : Prop where
  | idle (after : Ledger) (steps : Staged.Obligations.Step ledger after)
      (account : Accounted h after [] locals w.wg)
  | selected (items : List SkbId) (account : Accounted h ledger [] (⟨.selected,pid,items⟩::locals) w.wg)
      (pending : CreateDisposal.PendingBatch h ledger items)

/-- The original worker read and dequeue cuts conserve the same packet
lineage. Dequeue moves the actual queued occurrence to a selected local
owner before dispatch, independently of the later send/disposal outcome. -/
theorem Point.evidence (before : Accounted h ledger [] locals w.wg)
    (point : Point pid w h u middle) : Evidence ledger locals pid middle u := by
  cases point with
  | entry=>exact .idle ledger (.refl _) before
  | read performed=>exact .idle ledger (.refl _) (read_entry before performed).1
  | dropped read removed=>
    obtain ⟨atRead,cached⟩:=read_entry before read
    obtain ⟨atDrop,pending⟩:=drop atRead (cached _ _ rfl) removed
    exact .selected _ atDrop pending
  | selected performed=>
    obtain ⟨account,pending⟩:=(selection_returned before performed).accounted_entry
    exact .selected _ account pending
  | returned performed=>
    have returned:=Converse.Worker.transmit_cases pid before
    rw [performed] at returned
    obtain ⟨after,steps,account⟩:=returned.entry
    exact .idle after steps account

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSelector
