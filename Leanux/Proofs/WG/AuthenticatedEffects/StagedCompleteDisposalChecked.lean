import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSourceFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompletePurgeSource

/-! Bind-compatible paired accounting at actual purge and both peer-release
observers. Safe is derived from Accounted at the same ledger, including the
completed counted cut preceding a native Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations CompleteCarrier

/-- Actual counted purge preserves the paired carrier; native failure retains
its original accounting and does not fabricate a disposal receipt. -/
theorem purge (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe (CausalJournal.stagedPurge pid) := by
  intro w ambient history before
  obtain ⟨ledger,entry,complete⟩ := before
  have equation := Purge.run pid w ambient history
  change runPrefix ((CausalJournal.stagedPurge pid).run w) ambient history = _ at equation
  rw [equation]
  cases native : ((purgeStagedPackets pid).run w).run ambient with
  | error stop => exact ⟨[],by simp,accountSafe _ _ _ ⟨entry,complete⟩,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,clock⟩ := out
    cases value
    obtain ⟨part,generation,_,_,_,_,kept,finished,_⟩ :=
      StagedTerminalComplete.Source.purge_receipt pid ⟨(),w,v,ambient,clock⟩ native entry complete
    exact ⟨[.stagedDisposal (.purge pid ⟨(),w,v,ambient,clock⟩)],rfl,
      accountSafe _ _ _ ⟨kept,finished⟩,_,kept,finished⟩

theorem original_stopped (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (frontier : StagedTerminalComplete.Source.Original.Frontier ledger debts locals peer w ambient history stop last) :
    Safe last := by
  cases frontier with
  | cutStopped entry complete _ same =>
    subst last
    exact accountSafe _ _ _ ⟨entry,complete⟩
  | finishStopped pid p g clock afterLedger _ _ _ _ entry complete _ same =>
    subst last
    exact accountSafe _ _ _ ⟨entry,complete⟩

/-- Original peer repayment retains both accounting directions through the
exact source receipt and any failed timer/retirement continuation. -/
theorem original (peer : Option PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe (CausalJournal.peerRelease peer) := by
  intro w ambient history before
  obtain ⟨ledger,entry,complete⟩ := before
  obtain ⟨suffix,extended⟩ := original_appends peer w ambient history
  have result := StagedTerminalComplete.Source.Original.actual_cases peer ambient entry complete
  cases performed : runWGPrefix (CausalJournal.peerRelease peer) w ambient history with
  | mk outcome last =>
    rw [performed] at result
    change runPrefix ((CausalJournal.peerRelease peer).run w) ambient history = _ at performed
    rw [performed] at extended ⊢
    cases outcome with
    | error stop => exact ⟨suffix,extended,original_stopped Safe accountSafe result,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,clock⟩ := out
      cases value
      obtain ⟨value,g,a,afterLedger,_,_,_,_,_,kept,finished⟩ := result
      exact ⟨suffix,extended,accountSafe _ _ _ ⟨kept,finished⟩,afterLedger,kept,finished⟩

theorem nested_stopped (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (frontier : StagedTerminalComplete.Source.Nested.Frontier ledger debts locals peer w history stop last) :
    Safe last := by
  cases frontier with
  | cutStopped entry complete _ => exact accountSafe _ _ _ ⟨entry,complete⟩
  | finishStopped value g ambient cutHistory afterLedger _ _ _ _ entry complete same _ =>
    subst last
    exact accountSafe _ _ _ ⟨entry,complete⟩

/-- Nested TX peer repayment preserves the paired carrier at actual access
and release cuts, retaining its completed accounting on stopped suffixes. -/
theorem nested (peer : Option PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    PrefixEnsures (fun h w => Carrier debts locals h w.wg w.ambient) Safe
      (Admission.actualOps.release peer)
      (fun _ h w => Carrier debts locals h w.wg w.ambient) := by
  intro w history before
  obtain ⟨ledger,entry,complete⟩ := before
  obtain ⟨suffix,extended⟩ :=
    (CallbackQuiet.release (fun _ => (none : Option Unit)) (fun _ => rfl) (fun _ => rfl) peer).1 w history
  have result := StagedTerminalComplete.Source.Nested.actual_cases peer entry complete
  cases performed : runPrefix (Admission.actualOps.release peer) w history with
  | mk outcome last =>
    rw [performed] at result
    change (runPrefix (Admission.actualOps.release peer) w history).2 = _ at extended
    rw [performed] at extended
    cases outcome with
    | error stop => exact ⟨suffix,extended,nested_stopped Safe accountSafe result,True.intro⟩
    | ok out =>
      obtain ⟨value,v⟩ := out
      cases value
      obtain ⟨value,g,a,cutHistory,afterLedger,_,_,_,_,_,kept,finished⟩ := result
      exact ⟨suffix,extended,accountSafe _ _ _ ⟨kept,finished⟩,afterLedger,kept,finished⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
