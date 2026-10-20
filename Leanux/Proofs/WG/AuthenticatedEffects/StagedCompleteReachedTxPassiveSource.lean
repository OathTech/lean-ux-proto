import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSendingFrames

/-! Fixed completion prefixes before and after the ordered send loop.
The selected batch, original scope position and guard result are retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxPassive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch

private theorem unit_done (action : PrefixM CausalJournal.Event Unit) :
    (action >>= fun _=>pure ())=action := by
  have same : (fun _ : Unit=> (pure () : PrefixM CausalJournal.Event Unit))=pure := by
    funext value
    cases value
    rfl
  rw [same,bind_pure]

inductive PreludeStage where
  | start | marked | traversed | prepared

def preludeLeading (pid : PeerId) (items : List SkbId) : PreludeStage → PrefixM CausalJournal.Event Unit
  | .start=>pure ()
  | .marked=>CausalJournal.completionOps.completion pid items
  | .traversed=>do
      CausalJournal.completionOps.completion pid items
      CausalJournal.completionOps.traversal pid
  | .prepared=>WorkerCompletion.prelude pid items

def preludeTail (pid : PeerId) (items : List SkbId) : PreludeStage → PrefixM CausalJournal.Event Unit
  | .start=>WorkerCompletion.prelude pid items
  | .marked=>do
      CausalJournal.completionOps.traversal pid
      CausalJournal.completionOps.sent pid
  | .traversed=>CausalJournal.completionOps.sent pid
  | .prepared=>pure ()

theorem prelude_factor (pid : PeerId) (items : List SkbId) (stage : PreludeStage) :
    WorkerCompletion.prelude pid items=(preludeLeading pid items stage >>= fun _=>preludeTail pid items stage) := by
  cases stage <;> simp only [preludeLeading,preludeTail,WorkerCompletion.prelude,bind_assoc,pure_bind,unit_done]

def preludeRemaining (pid : PeerId) (items : List SkbId) (key : KeypairId) (position : Nat)
    (stage : PreludeStage) : PrefixM CausalJournal.Event Bool := do
  preludeTail pid items stage
  TxSending.tail pid items items key position false

theorem prelude_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (performed : runPrefix (preludeLeading pid items stage) u
      (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (preludeRemaining pid items head.keypair middle.length stage) v last := by
  rw [TxSending.selected_continuation selected]
  simp only [TxSending.scopedBody,TxSending.body,prelude_factor pid items stage,bind_assoc,
    runPrefix_bind,runPrefix_emit,performed,preludeRemaining,TxSending.tail]

inductive FinishStage where
  | start | guarded | data | fresh

def data (pid : PeerId) (flag : Bool) : PrefixM CausalJournal.Event Unit := do
  if flag then CausalJournal.completionOps.dataSent pid

def finishLeading (pid : PeerId) (sent : Bool) : FinishStage → PrefixM CausalJournal.Event Bool
  | .start=>pure sent
  | .guarded=>Completion.finishGuard sent
  | .data=>do
      let flag←Completion.finishGuard sent
      data pid flag
      pure flag
  | .fresh=>do
      let flag←Completion.finishGuard sent
      data pid flag
      CausalJournal.completionOps.fresh pid
      pure flag

def finishTail (pid : PeerId) (flag : Bool) : FinishStage → PrefixM CausalJournal.Event Unit
  | .start=>finish CausalJournal.completionOps pid flag
  | .guarded=>do
      data pid flag
      CausalJournal.completionOps.fresh pid
  | .data=>CausalJournal.completionOps.fresh pid
  | .fresh=>pure ()

theorem finish_factor (pid : PeerId) (sent : Bool) (stage : FinishStage) :
    finish CausalJournal.completionOps pid sent=(finishLeading pid sent stage >>= fun flag=>finishTail pid flag stage) := by
  cases stage with
  | start=>simp only [finishLeading,finishTail,pure_bind]
  | guarded | data | fresh=>
    simp only [finishLeading,finishTail,data,finish,Completion.finishGuard,bind_assoc,pure_bind,unit_done]
    congr 1
    funext ignored
    congr 1
    funext flag
    cases flag <;> simp only [Bool.false_eq_true,↓reduceIte,pure_bind]

def finishRemaining (pid : PeerId) (items : List SkbId) (key : KeypairId) (position : Nat)
    (stage : FinishStage) (flag : Bool) : PrefixM CausalJournal.Event Bool := do
  finishTail pid flag stage
  emitPrefix (.scope (.exited position))
  CausalJournal.completionOps.dispose pid items key

theorem finish_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (prepared : runPrefix (WorkerCompletion.prelude pid items) u
      (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last))
    (looped : runPrefix (sendLoop CausalJournal.completionOps pid items false) v last=(.ok (sent,q),after))
    (performed : runPrefix (finishLeading pid sent stage) q after=(.ok (flag,r),events)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (finishRemaining pid items head.keypair middle.length stage flag) r events := by
  rw [TxSending.loop_continuation selected prepared (List.append_nil items).symm looped]
  simp only [TxSending.tail,sendLoop,pure_bind,finish_factor pid sent stage,bind_assoc,runPrefix_bind,
    performed,finishRemaining]

inductive Point (pid : PeerId) (w : World) (h : List CausalJournal.Event) : World → List CausalJournal.Event → Prop where
  | prelude
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
      (performed : runPrefix (preludeLeading pid items stage) u
        (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last)) : Point pid w h v last
  | finish
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
      (prepared : runPrefix (WorkerCompletion.prelude pid items) u
        (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last))
      (looped : runPrefix (sendLoop CausalJournal.completionOps pid items false) v last=(.ok (sent,q),after))
      (performed : runPrefix (finishLeading pid sent stage) q after=(.ok (flag,r),events)) : Point pid w h r events

theorem Point.remaining (point : Point pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | prelude selected performed=>exact ⟨_,prelude_continuation selected performed⟩
  | finish selected prepared looped performed=>exact ⟨_,finish_continuation selected prepared looped performed⟩

noncomputable def remainder (point : Point pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxPassive
