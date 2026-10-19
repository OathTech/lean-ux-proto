import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxReadyFrames

/-! Branch composition at the actual selected worker cut. The crypted
completion theorem is an explicit callback obligation; the DEAD source is
fully discharged and retains its completed terminal cuts on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal HandshakeSecurity.StagedConservation
set_option pp.structureInstances false

def Returned (ledger : Ledger) (locals : List TxLocalBatch)
    (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ afterLedger, Staged.Obligations.Step ledger afterLedger ∧
    StagedEntry.Inv history afterLedger [] locals w.wg

abbrev CryptFailure := Ledger → List TxLocalBatch → PeerId → List SkbId → DataPacket →
  World → List CausalJournal.Event → Stop → List CausalJournal.Event → Prop

def CryptContract (failed : CryptFailure) : Prop :=
  ∀ (ledger : Ledger) (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId)
    (head : DataPacket) (w : World) (history : List CausalJournal.Event),
    StagedEntry.Inv history ledger [] (⟨.selected,pid,items⟩ :: locals) w.wg →
    PendingBatch history ledger items → head.state = .crypted →
    match (runPrefix (crypted pid items head) w history).1 with
    | .error stop => failed ledger locals pid items head w history stop
        (runPrefix (crypted pid items head) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (crypted pid items head) w history).2 v

inductive DispatchStop (failed : CryptFailure) (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history : List CausalJournal.Event) (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | crypted (u : World)
      (guarded : runPrefix (CausalJournal.completionOps.step (branch .txCrypted (head.state == .crypted)))
        w history = (.ok (true,u),history))
      (entry : StagedEntry.Inv history ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg)
      (pending : PendingBatch history ledger items)
      (performed : runPrefix (TxWorker.crypted pid items head) u history = (.error stop,last))
      (frontier : failed ledger locals pid items head u history stop last)
  | dead (u : World)
      (guarded : runPrefix (CausalJournal.completionOps.step (branch .txCrypted (head.state == .crypted)))
        w history = (.ok (false,u),history))
      (entry : StagedEntry.Inv history ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg)
      (pending : PendingBatch history ledger items)
      (performed : runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head)
        u history = (.error stop,last))
      (frontier : DeadEntry.DeadStop ledger [] locals pid items head u history stop last)

/-- At the original crypted/DEAD branch, ownership stays at the same
selected packet occurrence. Normal disposal restores empty caller debts;
a stopped branch retains its actual input and failed source cut. The
crypted callback remains an explicit local obligation. -/
theorem dispatch_cases (failed : CryptFailure) (completed : CryptContract failed)
    (pid : PeerId) (items : List SkbId) (head : DataPacket)
    (before : StagedEntry.Inv history ledger [] (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    match (runPrefix (dispatch pid items head) w history).1 with
    | .error stop => DispatchStop failed ledger locals pid items head w history stop
        (runPrefix (dispatch pid items head) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (dispatch pid items head) w history).2 v := by
  obtain ⟨u,guarded,same⟩ := guard .txCrypted (head.state == .crypted) w history
  have entry : StagedEntry.Inv history ledger [] (⟨.selected,pid,items⟩ :: locals) u.wg := by
    simpa only [same] using before
  unfold dispatch
  rw [runPrefix_bind,guarded]
  simp only []
  cases state : (head.state == .crypted) with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    have result := DeadEntry.dead_cases pid items head entry pending
    cases performed : runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
        CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) u history with
    | mk outcome last =>
      rw [performed] at result
      cases outcome with
      | error stop =>
        exact .dead u (by simpa only [state] using guarded) entry pending performed result
      | ok out =>
        obtain ⟨value,v⟩ := out
        obtain ⟨_,afterLedger,step,final,_⟩ := result
        exact ⟨afterLedger,step,final⟩
  | true =>
    simp only [↓reduceIte]
    have marked : head.state = .crypted := by
      cases actual : head.state with
      | crypted => rfl
      | uncrypted => rw [actual] at state; cases state
      | dead => rw [actual] at state; cases state
    have result := completed ledger locals pid items head u history entry pending marked
    cases performed : runPrefix (crypted pid items head) u history with
    | mk outcome last =>
      rw [performed] at result
      cases outcome with
      | error stop =>
        exact .crypted u (by simpa only [state] using guarded) entry pending performed result
      | ok out => exact result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
