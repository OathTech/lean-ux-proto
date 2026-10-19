import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionEntryAheadSource

/-! The guarded crypt-ahead branch reaches the nested encryption iteration
at its actual requeued state. Poll, softirq, encryption and later bookkeeping
failures keep their original runs and the carrier at the corresponding cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompleteCarrier

structure AheadPath (pid : PeerId) (w : World) (history : List CausalJournal.Event)
    (enc : Activation) (ledger : Ledger) (u : World) (middle : List CausalJournal.Event) : Prop where
  performed : runPrefix (aheadPrefix pid) w history = (.ok (some enc,u),middle)
  carrier : CompleteProduct.Carrier middle u
  accounted : Accounted middle ledger [] [] u.wg
  extended : ∃ suffix, middle = history ++ suffix

theorem ahead_path (pid : PeerId) (before : CompleteProduct.Carrier history w)
    (performed : runPrefix (aheadPrefix pid) w history = (.ok (some enc,u),middle)) :
    ∃ ledger, AheadPath pid w history enc ledger u middle := by
  obtain ⟨suffix,grown,_,kept⟩ := ahead_prefix_checked pid w history before
  simp only [performed] at grown kept
  obtain ⟨ledger,accounted⟩ := kept.1
  exact ⟨ledger,performed,kept,accounted,⟨suffix,grown⟩⟩

theorem AheadPath.original (path : AheadPath pid w history enc ledger u middle) :
    runPrefix (Driver.cryptAheadObserved CausalJournal.hooks pid) w history =
      runPrefix (Driver.encryptIterObserved CausalJournal.hooks >>= aheadFinish pid enc) u middle := by
  rw [ahead_factor,runPrefix_bind,path.performed]
  rfl

def nestedPrefix (pid : PeerId) : PrefixM CausalJournal.Event (Option (Activation × Option (List SkbId))) := do
  let some enc ← aheadPrefix pid | return none
  let item ← entryPrefix
  pure (some (enc,item))

theorem AheadPath.nested_entry (path : AheadPath pid w history enc ledger u middle)
    (entry : EntryPath item u middle encryptLedger v after) :
    runPrefix (nestedPrefix pid) w history = (.ok (some (enc,item),v),after) ∧
      CompleteProduct.Carrier after v ∧ Accounted after encryptLedger [] [] v.wg := by
  refine ⟨?_,entry.carrier,entry.accounted⟩
  rw [nestedPrefix,runPrefix_bind,path.performed]
  change runPrefix (entryPrefix >>= fun item => pure (some (enc,item))) u middle = _
  rw [runPrefix_bind,entry.performed]
  rfl

inductive AheadStopped (pid : PeerId) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | guards (performed : runPrefix (aheadPrefix pid) w history = (.error reason,last))
      (safe : CompleteProduct.Safe last)
  | nested (enc : Activation) (ledger : Ledger) (u : World) (middle : List CausalJournal.Event)
      (path : AheadPath pid w history enc ledger u middle)
      (performed : runPrefix (Driver.encryptIterObserved CausalJournal.hooks) u middle = (.error reason,last))
      (stopped : Stopped u middle reason last)
  | finish (enc : Activation) (ledger : Ledger) (u : World) (middle : List CausalJournal.Event)
      (path : AheadPath pid w history enc ledger u middle)
      (result : IterResult) (afterLedger : Ledger) (v : World) (after : List CausalJournal.Event)
      (encrypted : runPrefix (Driver.encryptIterObserved CausalJournal.hooks) u middle = (.ok (result,v),after))
      (carrier : CompleteProduct.Carrier after v)
      (accounted : Accounted after afterLedger [] [] v.wg)
      (performed : runPrefix (aheadFinish pid enc result) v after = (.error reason,last))

theorem AheadStopped.source_failed (stopped : AheadStopped pid w history reason last) :
    runPrefix (Driver.cryptAheadObserved CausalJournal.hooks pid) w history = (.error reason,last) := by
  cases stopped with
  | guards performed _ => rw [ahead_factor,runPrefix_bind,performed]
  | nested _ _ _ _ path performed _ => rw [path.original,runPrefix_bind,performed]
  | finish _ _ _ _ path _ _ _ _ encrypted _ _ performed =>
    rw [path.original,runPrefix_bind,encrypted]
    exact performed

/-- Earlier guard failures, nested iteration failures and later bookkeeping
failures are all chosen from the original observed execution. -/
theorem ahead_failed (pid : PeerId) (before : CompleteProduct.Carrier history w)
    (failed : runPrefix (Driver.cryptAheadObserved CausalJournal.hooks pid) w history = (.error reason,last)) :
    AheadStopped pid w history reason last := by
  rw [ahead_factor,runPrefix_bind] at failed
  cases selected : runPrefix (aheadPrefix pid) w history with
  | mk outcome middle =>
    rw [selected] at failed
    cases outcome with
    | error stop =>
      cases failed
      obtain ⟨_,_,safe,_⟩ := ahead_prefix_checked pid w history before
      exact .guards selected (by simpa only [selected] using safe)
    | ok out =>
      obtain ⟨option,u⟩ := out
      cases option with
      | none => simp only [aheadBranch,runPrefix_pure] at failed; cases failed
      | some enc =>
        obtain ⟨ledger,path⟩ := ahead_path pid before selected
        change runPrefix (Driver.encryptIterObserved CausalJournal.hooks >>= aheadFinish pid enc) u middle =
          (.error reason,last) at failed
        rw [runPrefix_bind] at failed
        cases encrypted : runPrefix (Driver.encryptIterObserved CausalJournal.hooks) u middle with
        | mk result after =>
          rw [encrypted] at failed
          cases result with
          | error stop =>
            cases failed
            exact .nested enc ledger u middle path encrypted (iteration_failed path.carrier encrypted)
          | ok out =>
            obtain ⟨value,v⟩ := out
            obtain ⟨_,_,_,kept⟩ := CompleteProduct.encrypt_iteration u middle path.carrier
            simp only [encrypted] at kept
            obtain ⟨afterLedger,accounted⟩ := kept.1
            exact .finish enc ledger u middle path value afterLedger v after encrypted kept accounted failed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
