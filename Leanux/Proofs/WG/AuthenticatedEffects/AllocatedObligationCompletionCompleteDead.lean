import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteWorkerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateLoop
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteNestedRelease

/-! The actual DEAD free loop and subsequent repayments transport Entry and
terminal completeness on one ledger. A stopped repayment retains the real
completed free cut and the exact nested-release successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Dead
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete StagedEntry.CompleteCarrier
open CreateDisposal HandshakeSecurity.StagedConservation

private theorem key_history (key : KeypairId) :
    HistoryFrame ledgerEvent? (Admission.actualOps.access (keypairPutPrefix (some key) false)) :=
  focusPrefix_other _ _ _ (fun _ => rfl) _

inductive RepayStopped (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (key : KeypairId) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | keyStopped (accounted : Accounted last ledger debts locals w.wg)
      (failed : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false))
        w history = (.error reason,last))
  | peerStopped (u : World) (middle : List CausalJournal.Event)
      (keyRun : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false))
        w history = (.ok ((),u),middle))
      (accounted : Accounted middle ledger debts locals u.wg)
      (frontier : Source.Nested.Frontier ledger debts locals (some pid) u middle reason last)

def RepayReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (key : KeypairId) (w : World) (history last : List CausalJournal.Event)
    (value : Bool) (v : World) : Prop :=
  value = true ∧ ∃ u middle,
    runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false))
      w history = (.ok ((),u),middle) ∧ Accounted middle ledger debts locals u.wg ∧
    runPrefix (Admission.actualOps.release (some pid)) u middle = (.ok ((),v),last) ∧
    Source.Nested.Returned ledger debts locals (some pid) u middle last v

theorem repay_cases (pid : PeerId) (key : KeypairId)
    (before : Accounted history ledger debts locals w.wg) :
    match (runPrefix (DeadEntry.repay pid key) w history).1 with
    | .error reason => RepayStopped ledger debts locals pid key w history reason
        (runPrefix (DeadEntry.repay pid key) w history).2
    | .ok (value,v) => RepayReturned ledger debts locals pid key w history
        (runPrefix (DeadEntry.repay pid key) w history).2 value v := by
  have complete : Complete (runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false)) w history).2 ledger :=
    history_preserved before.complete (Appends.focus _ _ _) (key_history key) (w := w)
  unfold DeadEntry.repay
  simp only [runPrefix_bind]
  cases keyRun : runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false)) w history with
  | mk result middle =>
    rw [keyRun] at complete
    cases result with
    | error reason =>
      have entry := entry_history before.entry (Appends.focus _ _ _) (key_history key) w
      change StagedEntry.Inv (runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false)) w history).2 ledger debts locals w.wg at entry
      rw [keyRun] at entry
      exact .keyStopped ⟨entry,complete⟩ keyRun
    | ok out =>
      obtain ⟨ignored,u⟩ := out
      cases ignored
      have entry := DeadEntry.key_entry key before.entry keyRun
      have released := Source.Nested.actual_cases (some pid) entry complete
      simp only []
      cases peerRun : runPrefix (Admission.actualOps.release (some pid)) u middle with
      | mk result last =>
        rw [peerRun] at released
        cases result with
        | error reason => exact .peerStopped u middle keyRun ⟨entry,complete⟩ released
        | ok out =>
          obtain ⟨ignored,v⟩ := out
          cases ignored
          exact ⟨rfl,u,middle,keyRun,⟨entry,complete⟩,peerRun,released⟩

theorem RepayReturned.entry
    (returned : RepayReturned ledger debts locals pid key w history last value v) :
    ∃ after, Staged.Obligations.Step ledger after ∧ Accounted last after debts locals v.wg := by
  obtain ⟨_,_,_,_,_,_,released⟩ := returned
  obtain ⟨_,_,_,_,after,_,_,step,_,_,entry,complete⟩ := released
  exact ⟨after,step,entry,complete⟩

theorem RepayStopped.accounted
    (frontier : RepayStopped ledger debts locals pid key w history reason last) :
    ∃ after cut, Staged.Obligations.Step ledger after ∧ Accounted last after debts locals cut := by
  cases frontier with
  | keyStopped accounted _ => exact ⟨ledger,w.wg,.refl _,accounted⟩
  | peerStopped u _ _ _ stopped =>
    cases stopped with
    | cutStopped entry complete _ => exact ⟨ledger,u.wg,.refl _,entry,complete⟩
    | finishStopped _ g _ _ after _ step _ _ entry complete same _ =>
      exact ⟨after,g,step,(by simpa only [same] using entry),(by simpa only [same] using complete)⟩

inductive Stopped (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history : List CausalJournal.Event) (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | atRepay (u : World) (suffix : List CausalJournal.Event) (afterFree : Ledger)
      (freed : runPrefix (loop (.deadBatch pid head) items) w history = (.ok ((),u),history ++ suffix))
      (step : Staged.Obligations.Step ledger afterFree)
      (accounted : Accounted (history ++ suffix) afterFree debts locals u.wg)
      (dropped : AllDropped (history ++ suffix) afterFree (.deadBatch pid head) items)
      (failed : runPrefix (DeadEntry.repay pid head.keypair) u (history ++ suffix) = (.error reason,last))
      (frontier : RepayStopped afterFree debts locals pid head.keypair u (history ++ suffix) reason last)

def Returned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history last : List CausalJournal.Event) (value : Bool) (v : World) : Prop :=
  ∃ u suffix afterFree,
    runPrefix (loop (.deadBatch pid head) items) w history = (.ok ((),u),history ++ suffix) ∧
    Staged.Obligations.Step ledger afterFree ∧ Accounted (history ++ suffix) afterFree debts locals u.wg ∧
    AllDropped (history ++ suffix) afterFree (.deadBatch pid head) items ∧
    runPrefix (DeadEntry.repay pid head.keypair) u (history ++ suffix) = (.ok (value,v),last) ∧
    RepayReturned afterFree debts locals pid head.keypair u (history ++ suffix) last value v

theorem dead_cases (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    match (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).1 with
    | .error reason => Stopped ledger debts locals pid items head w history reason
        (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
          CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).2
    | .ok (value,v) => Returned ledger debts locals pid items head w history
        (runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
          CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) w history).2 value v := by
  rw [DeadEntry.dead_factor,runPrefix_bind]
  obtain ⟨u,suffix,afterFree,freed,step,atRepay,dropped⟩ :=
    StagedEntry.CompleteCreate.free_loop (.deadBatch pid head) .selected items before pending
  rw [freed]
  simp only []
  have result := repay_cases pid head.keypair atRepay
  cases performed : runPrefix (DeadEntry.repay pid head.keypair) u (history ++ suffix) with
  | mk outcome last =>
    rw [performed] at result
    cases outcome with
    | error reason => exact .atRepay u suffix afterFree freed step atRepay dropped performed result
    | ok out => exact ⟨u,suffix,afterFree,freed,step,atRepay,dropped,performed,result⟩

theorem Returned.entry (returned : Returned ledger debts locals pid items head w history last value v) :
    ∃ after, Staged.Obligations.Step ledger after ∧ Accounted last after debts locals v.wg := by
  obtain ⟨_,_,_,_,step,_,_,_,repay⟩ := returned
  obtain ⟨after,steps,accounted⟩ := repay.entry
  exact ⟨after,step.trans steps,accounted⟩

theorem Stopped.accounted (frontier : Stopped ledger debts locals pid items head w history reason last) :
    ∃ after cut, Staged.Obligations.Step ledger after ∧ Accounted last after debts locals cut := by
  cases frontier with
  | atRepay _ _ _ _ step _ _ _ stopped =>
    obtain ⟨after,cut,steps,accounted⟩ := stopped.accounted
    exact ⟨after,cut,step.trans steps,accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Dead
