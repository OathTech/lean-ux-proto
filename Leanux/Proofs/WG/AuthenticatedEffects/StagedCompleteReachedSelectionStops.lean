import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionPath

/-! The original recursive worker frontier determines whether selection
itself stopped or a concrete selected callback was reached. No accounted
snapshot is reconstructed from an existential endpoint certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

inductive CallbackStopped (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (w : World) (history : List CausalJournal.Event) (reason : Stop)
    (last : List CausalJournal.Event) : Selected → Prop where
  | crypted (items : List SkbId) (head : DataPacket)
      (performed : runPrefix (TxWorker.crypted pid items head) w history = (.error reason,last))
      (interval : WorkerInterval ledger locals pid items head w history (.error reason) last) :
      CallbackStopped ledger locals pid w history reason last ⟨items,head,true⟩
  | dead (items : List SkbId) (head : DataPacket)
      (performed : runPrefix (selectedCallback pid (some ⟨items,head,false⟩)) w history =
        (.error reason,last))
      (frontier : Converse.Dead.Stopped ledger [] locals pid items head w history reason last) :
      CallbackStopped ledger locals pid w history reason last ⟨items,head,false⟩

inductive SelectionStop (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId)
    (w : World) (history : List CausalJournal.Event) (reason : Stop)
    (last : List CausalJournal.Event) : Prop where
  | selecting (performed : runPrefix (workerSelection pid) w history = (.error reason,last))
  | selected (picked : Selected) (v : World) (middle : List CausalJournal.Event)
      (path : SelectionPath ledger locals pid w history picked v middle)
      (callback : CallbackStopped ledger locals pid v middle reason last picked)

/-- The original worker's stopped frontier supplies a fixed selection
prefix and its exact callback entry. A crypted callback keeps the original
scoped send/disposal interval, including an open sending-internal frontier. -/
theorem selection_stop
    (before : Accounted history ledger [] locals w.wg)
    (frontier : Converse.Worker.TransmitStop ledger locals pid w history reason last) :
    SelectionStop ledger locals pid w history reason last := by
  cases frontier with
  | peek _ failed =>
    apply SelectionStop.selecting
    simp only [workerSelection,runPrefix_bind,failed]
  | body first pw ph peeked atPeek cached body =>
    cases body with
    | ready _ failed =>
      apply SelectionStop.selecting
      simp only [workerSelection,bodySelection,runPrefix_bind,peeked,failed]
    | packet rw rh items id readied chosen nonempty _ failed =>
      subst first
      apply SelectionStop.selecting
      simp only [workerSelection,bodySelection,runPrefix_bind,peeked,readied,
        Bool.not_true,Bool.false_eq_true,↓reduceIte,nonempty,failed]
    | afterRead rw sw rh sh items id head readied chosen nonempty read atRead afterRead =>
      subst first
      cases afterRead with
      | drop _ _ failed =>
        apply SelectionStop.selecting
        simp only [workerSelection,bodySelection,afterReadSelection,runPrefix_bind,peeked,readied,
          Bool.not_true,Bool.false_eq_true,↓reduceIte,nonempty,read,failed]
      | dispatch dw dh removed atDrop pending dispatch =>
        cases dispatch with
        | crypted v guarded atGuard pending performed stopped =>
          have interval := worker_interval pid items head atGuard.entry atGuard.complete pending
          rw [performed] at interval
          exact .selected ⟨items,head,true⟩ v dh
            (.intro pw rw sw dw ph rh sh id before peeked readied nonempty read atRead
              removed atDrop guarded atGuard pending)
            (.crypted items head performed interval)
        | dead v guarded atGuard pending performed stopped =>
          exact .selected ⟨items,head,false⟩ v dh
            (.intro pw rw sw dw ph rh sh id before peeked readied nonempty read atRead
              removed atDrop guarded atGuard pending)
            (.dead items head performed stopped)

theorem CallbackStopped.run
    (stopped : CallbackStopped ledger locals pid w history reason last picked) :
    runPrefix (selectedCallback pid (some picked)) w history = (.error reason,last) := by
  cases stopped with
  | crypted _ _ performed => exact performed
  | dead _ _ performed => exact performed

theorem SelectionStop.run
    (stopped : SelectionStop ledger locals pid w history reason last) :
    runPrefix (CausalJournal.transmit pid) w history = (.error reason,last) := by
  cases stopped with
  | selecting performed => rw [worker_selection_factor,runPrefix_bind,performed]
  | selected _ _ _ path callback => rw [path.callback_run,callback.run]

theorem transmit_selection_stop (pid : PeerId)
    (before : Accounted history ledger [] locals w.wg)
    (failed : runPrefix (CausalJournal.transmit pid) w history = (.error reason,last)) :
    SelectionStop ledger locals pid w history reason last := by
  have result := Converse.Worker.transmit_cases pid before
  rw [failed] at result
  exact selection_stop before result

/-- The source-specific projection is accompanied by the full original
recursive frontier. In particular a Stop before callback selection retains
all of its earlier native runs instead of only an existential saved world. -/
theorem transmit_stopped_cut (pid : PeerId)
    (before : Accounted history ledger [] locals w.wg)
    (failed : runPrefix (CausalJournal.transmit pid) w history = (.error reason,last)) :
    Converse.Worker.TransmitStop ledger locals pid w history reason last ∧
      SelectionStop ledger locals pid w history reason last := by
  have original := Converse.Worker.transmit_cases pid before
  rw [failed] at original
  exact ⟨original,selection_stop before original⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
