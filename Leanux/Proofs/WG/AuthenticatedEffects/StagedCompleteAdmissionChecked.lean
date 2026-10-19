import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdmissionFrames

/-! The actual createData admission returns paired accounting in its real
unpublished/queued phase. Stops retain the original source frontier and a
paired account at that reached ownership cut, extended only by actual events. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier

theorem admission_stopped (Safe : List Event → Prop)
    (accountSafe : ∀ locals h w, Accounted h ledger debts locals w → Safe h)
    (frontier : CreateEntry.FrontStop ledger debts locals pid items w history stop last)
    (complete : Complete last ledger) : Safe last := by
  cases frontier with
  | readStopped entry failed =>
    exact accountSafe _ _ _ (focused_stopped _ entry complete failed)
  | enqueueStopped p u v readHistory read guard frontier =>
    cases frontier with
    | beforeStopped entry failed => exact accountSafe _ _ _ (focused_stopped _ entry complete failed)
    | queuedStopped p u v readHistory writes read installed entry failed =>
      exact accountSafe _ _ _ (focused_stopped _ entry complete failed)
  | publicationStopped p u v q r readHistory queuedHistory read guard enqueued pipe entry failed =>
    obtain ⟨suffix,extended,quiet⟩ := Publication.birth_quiet items .dead r queuedHistory
    rw [failed] at extended
    change last = queuedHistory ++ suffix at extended
    apply accountSafe locals last r.wg
    refine ⟨?_,complete⟩
    rw [extended]
    exact entry.views suffix quiet rfl rfl rfl rfl rfl rfl

def AdmissionReturned (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (ret : Int) (history : List Event) (w : World) : Prop :=
  ((ret = -EINVAL ∨ ret = -WG.ENOSPC) ∧ Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) ∨
    ((ret = 0 ∨ ret = -WG.EPIPE) ∧ Accounted history ledger debts locals w.wg)

/-- The terminal-converse companion follows actual admission, including its
borrow-funded nonfinal publication repayment; the original ownership frontier
is retained on Stop rather than replaced by historical completeness. -/
theorem admission_cases {w : World} (pid : PeerId) (items : List SkbId)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) :
    Complete (runPrefix (Admission.actual pid items) w history).2 ledger ∧
      match (runPrefix (Admission.actual pid items) w history).1 with
      | .error stop => CreateEntry.FrontStop ledger debts locals pid items w history stop
          (runPrefix (Admission.actual pid items) w history).2
      | .ok (ret,v) => AdmissionReturned ledger debts locals pid items ret
          (runPrefix (Admission.actual pid items) w history).2 v := by
  obtain ⟨_,_,complete,_⟩ := admission_history pid items w history before.complete
  have own := CreateEntry.front_cases pid items before.entry
  refine ⟨complete,?_⟩
  cases performed : (runPrefix (Admission.actual pid items) w history).1 with
  | error stop => simpa only [performed] using own
  | ok out =>
    obtain ⟨ret,v⟩ := out
    rw [performed] at own
    rcases own with ⟨code,entry⟩ | ⟨code,entry⟩
    · exact Or.inl ⟨code,entry,complete⟩
    · exact Or.inr ⟨code,entry,complete⟩

/-- Bind-compatible actual admission keeps the same ledger while transferring
its unpublished local exactly at enqueue. Final refusal cleanup is a separate
source suffix and is not framed as unchanged-ledger admission. -/
theorem admission (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (Safe : List Event → Prop)
    (accountSafe : ∀ locals h w, Accounted h ledger debts locals w → Safe h) :
    PrefixEnsures (fun h w => Accounted h ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg) Safe
      (Admission.actual pid items)
      (fun ret h w => AdmissionReturned ledger debts locals pid items ret h w) := by
  intro w history before
  obtain ⟨suffix,extended⟩ := Admission.actual_appends pid items w history
  have result := admission_cases pid items before
  cases performed : runPrefix (Admission.actual pid items) w history with
  | mk outcome last =>
    rw [performed] at result extended
    cases outcome with
    | error stop => exact ⟨suffix,extended,admission_stopped Safe accountSafe result.2 result.1,True.intro⟩
    | ok out =>
      obtain ⟨ret,v⟩ := out
      refine ⟨suffix,extended,?_,result.2⟩
      rcases result.2 with ⟨_,entry⟩ | ⟨_,entry⟩
      · exact accountSafe _ _ _ entry
      · exact accountSafe _ _ _ entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
