import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteDead

/-! The selected branch keeps paired accounting and the actual branch
completion witness. The crypted and DEAD contracts are discharged on the
same entry ledger, including their exact stopped source cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal HandshakeSecurity.StagedConservation
open StagedEntry.CompleteCarrier StagedTerminalComplete TxWorker
set_option pp.structureInstances false

inductive Returned (ledger : Ledger) (locals : List TxLocalBatch)
    (last : List CausalJournal.Event) (v : World) : Prop where
  | idle (accounted : Accounted last ledger [] locals v.wg)
  | crypted (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
      (history : List CausalJournal.Event) (value : Bool)
      (source : Converse.WorkerReturned ledger locals pid items head w history last value v)
  | dead (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
      (history : List CausalJournal.Event) (value : Bool)
      (source : Dead.Returned ledger [] locals pid items head w history last value v)

theorem Returned.entry (returned : Returned ledger locals last v) :
    ∃ after, Staged.Obligations.Step ledger after ∧ Accounted last after [] locals v.wg := by
  cases returned with
  | idle accounted => exact ⟨ledger,.refl _,accounted⟩
  | crypted _ _ _ _ _ _ source =>
    obtain ⟨after,step,entry,complete⟩ := source.entry
    exact ⟨after,step,entry,complete⟩
  | dead _ _ _ _ _ _ source => exact source.entry

inductive DispatchStop (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history : List CausalJournal.Event) (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | crypted (u : World)
      (guarded : runPrefix (CausalJournal.completionOps.step (branch .txCrypted (head.state == .crypted)))
        w history = (.ok (true,u),history))
      (entry : Accounted history ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg)
      (pending : PendingBatch history ledger items)
      (performed : runPrefix (TxWorker.crypted pid items head) u history = (.error stop,last))
      (frontier : Converse.WorkerFailure ledger locals pid items head u history stop last)
  | dead (u : World)
      (guarded : runPrefix (CausalJournal.completionOps.step (branch .txCrypted (head.state == .crypted)))
        w history = (.ok (false,u),history))
      (entry : Accounted history ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg)
      (pending : PendingBatch history ledger items)
      (performed : runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head)
        u history = (.error stop,last))
      (frontier : Dead.Stopped ledger [] locals pid items head u history stop last)

/-- At the original crypted/DEAD branch, ownership stays at the same
selected packet occurrence. Normal disposal restores empty caller debts;
a stopped branch retains its actual input and failed source cut. Both
native branch callbacks are discharged. -/
theorem dispatch_cases
    (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : Accounted history ledger [] (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    match (runPrefix (TxWorker.dispatch pid items head) w history).1 with
    | .error stop => DispatchStop ledger locals pid items head w history stop
        (runPrefix (TxWorker.dispatch pid items head) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (TxWorker.dispatch pid items head) w history).2 v := by
  obtain ⟨u,guarded,same⟩ := guard .txCrypted (head.state == .crypted) w history
  have entry : Accounted history ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg := by
    simpa only [same] using before
  unfold TxWorker.dispatch
  rw [runPrefix_bind,guarded]
  simp only []
  cases state : (head.state == .crypted) with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    have result := Dead.dead_cases pid items head entry pending
    cases performed : runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) u history with
    | mk outcome last =>
      rw [performed] at result
      cases outcome with
      | error stop =>
        exact .dead u (by simpa only [state] using guarded) entry pending performed result
      | ok out =>
        obtain ⟨value,v⟩ := out
        exact .dead pid items head u history value result
  | true =>
    simp only [↓reduceIte]
    have marked : head.state = .crypted := by
      cases actual : head.state with
      | crypted => rfl
      | uncrypted => rw [actual] at state; cases state
      | dead => rw [actual] at state; cases state
    have result := Converse.crypted_contract ledger locals pid items head u history entry.entry entry.complete pending marked
    cases performed : runPrefix (crypted pid items head) u history with
    | mk outcome last =>
      rw [performed] at result
      cases outcome with
      | error stop =>
        exact .crypted u (by simpa only [state] using guarded) entry pending performed result
      | ok out => exact .crypted pid items head u history out.1 result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
