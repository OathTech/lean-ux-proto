import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSelectionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionReturned

/-! Exact TX worker continuations before dequeue and before dispatch. These
cuts do not require a later guard, send or disposal to return successfully. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSelector
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedConservation

def readBody (first : Option (List SkbId)) : PrefixM CausalJournal.Event (Option (List SkbId × DataPacket)) := do
  let go←TxWorker.ready first
  if !go then return none
  let some items:=first | CausalJournal.completionOps.step (invariant "unreachable")
  let some id:=items.head? | CausalJournal.completionOps.step (invariant "an empty ring item")
  let head←CausalJournal.completionOps.packet id
  pure (some (items,head))

def readTail (pid : PeerId) : Option (List SkbId × DataPacket) → PrefixM CausalJournal.Event Bool
  | none=>pure false
  | some (items,head)=>TxWorker.afterRead pid items head

theorem body_read_factor (pid : PeerId) (first : Option (List SkbId)) :
    TxWorker.body pid first=(readBody first >>= readTail pid) := by
  unfold TxWorker.body readBody
  simp only [bind_assoc]
  congr 1
  funext go
  cases go <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,pure_bind,readTail]
  cases first with
  | none=>rfl
  | some items=>
    cases chosen : items.head? with
    | none=>simp only [chosen];rfl
    | some id=>simp only [chosen,bind_assoc,pure_bind,readTail]

theorem read_factor (pid : PeerId) :
    CausalJournal.transmit pid=(workerReadPrefix pid >>= readTail pid) := by
  rw [TxWorker.transmit_factor]
  change (TxSelection.peek pid >>= fun first=>TxWorker.body pid first)=
    ((TxSelection.peek pid >>= readBody) >>= readTail pid)
  rw [bind_assoc]
  congr 1
  funext first
  exact body_read_factor pid first

theorem read_continuation
    (performed : runPrefix (workerReadPrefix pid) w h=(.ok (result,u),middle)) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (readTail pid result) u middle := by
  rw [read_factor,runPrefix_bind,performed]

theorem drop_continuation
    (read : runPrefix (workerReadPrefix pid) w h=(.ok (some (items,head),u),middle))
    (removed : runPrefix (CausalJournal.completionOps.drop pid items) u middle=(.ok ((),v),last)) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (TxWorker.dispatch pid items head) v last := by
  rw [read_continuation read,readTail,TxWorker.afterRead_factor,runPrefix_bind,removed]

inductive Point (pid : PeerId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | entry : Point pid w h w h
  | read (performed : runPrefix (workerReadPrefix pid) w h=(.ok (result,u),middle)) : Point pid w h u middle
  | dropped (read : runPrefix (workerReadPrefix pid) w h=(.ok (some (items,head),u),middle))
      (removed : runPrefix (CausalJournal.completionOps.drop pid items) u middle=(.ok ((),v),last)) :
      Point pid w h v last
  | selected (performed : runPrefix (workerSelection pid) w h=(.ok (some picked,u),middle)) : Point pid w h u middle
  | returned (performed : runPrefix (CausalJournal.transmit pid) w h=(.ok (value,u),middle)) : Point pid w h u middle

theorem Point.remaining (point : Point pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | read performed=>exact ⟨_,read_continuation performed⟩
  | dropped read removed=>exact ⟨_,drop_continuation read removed⟩
  | selected performed=>exact ⟨_,by rw [worker_selection_factor,runPrefix_bind,performed]⟩
  | returned performed=>exact ⟨pure _,performed⟩

noncomputable def remainder (point : Point pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSelector
