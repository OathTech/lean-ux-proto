import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateSource

/-! Bind-compatible actual creation preserves paired accounting. Stopped
safety is derived from the real saved account and source prefix; it is not an
additional whole-campaign conservation assumption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier StagedTerminalComplete
open Staged.Obligations CreateDisposal HandshakeSecurity.StagedConservation

theorem repayment_stopped (Safe : List CausalJournal.Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h)
    (frontier : RepaymentStop ledger debts locals pid first ret w history stop last) : Safe last := by
  cases frontier with
  | keyStopped u v accepted pipe before complete failed =>
    obtain ⟨_,_,entry,_⟩ := key_entry_history v.wg first v history before.entry
    rw [failed] at entry
    exact accountSafe _ _ _ _ ⟨entry,complete⟩
  | peerStopped u v z keyHistory accepted pipe key frontier =>
    exact CompleteSource.nested_stopped Safe (fun ledger h w account => accountSafe ledger locals h w account) frontier

theorem created_stopped (Safe : List CausalJournal.Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h)
    (frontier : CreatedStop ledger debts locals pid items w history stop last) : Safe last := by
  cases frontier with
  | emptyStopped empty before failed =>
    have complete := CompleteSource.focused_complete
      (liftPrefix (liftWG (invariant "an empty ring item" : WG.M Unit))) w before.complete
    change Complete (runPrefix (Admission.actualOps.step (invariant "an empty ring item") : PrefixM CausalJournal.Event Unit)
      w history).2 ledger at complete
    rw [failed] at complete
    exact accountSafe _ _ _ _ (CompleteSource.focused_stopped _ before.entry complete failed)
  | frontStopped first head frontier complete =>
    exact CompleteSource.admission_stopped Safe (accountSafe ledger) frontier complete
  | repaymentStopped first ret u middle head admission code frontier =>
    exact repayment_stopped Safe accountSafe frontier

/-- The actual shared creation callback preserves both fixed-ticket ownership
and exact receipt accounting, including every stopped prefix. Normal return
restores the caller's original debts and locals; PendingBatch remains the
explicit source-derived allocation precondition. -/
theorem checked (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (Safe : List CausalJournal.Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixEnsures
      (fun h w _ => Accounted h ledger debts (⟨.unpublished,pid,items⟩ :: locals) w ∧
        PendingBatch h ledger items)
      Safe (CausalJournal.create pid items) (fun _ => Carrier debts locals) := by
  intro w a history before
  have result := create_cases pid items (w := NativeAdapter.world w a) before.1 before.2
  obtain ⟨suffix,extended⟩ := (CausalJournal.CallbackQuiet.create (fun _ => (none : Option Unit))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items).1 w a history
  refine ⟨suffix,extended,?_⟩
  have lowered := NativeAdapter.run_lower
    (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items) w a history
  change runPrefix ((CausalJournal.create pid items).run w) a history = _ at lowered
  rw [lowered]
  cases performed : runPrefix (Terminal.createObserved CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items)
      (NativeAdapter.world w a) history with
  | mk outcome last =>
    rw [performed] at result
    cases outcome with
    | error stop => exact ⟨created_stopped Safe accountSafe result,True.intro⟩
    | ok out =>
      obtain ⟨ignored,v⟩ := out
      cases ignored
      obtain ⟨first,ret,u,middle,afterLedger,_,_,_,account,_⟩ := result
      exact ⟨accountSafe _ _ _ _ account,afterLedger,account⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteCreate
