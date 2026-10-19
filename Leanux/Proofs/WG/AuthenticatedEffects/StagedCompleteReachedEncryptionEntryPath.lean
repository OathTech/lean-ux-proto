import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionEntrySource

/-! Exact poll and softirq paths, each retaining the complete carrier at its
actual returned state. The selected item comes only from that same poll run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompleteCarrier

structure PollPath (item : Option (List SkbId)) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (u : World) (middle : List CausalJournal.Event) : Prop where
  performed : runPrefix CausalJournal.hooks.poll w history = (.ok (item,u),middle)
  carrier : CompleteProduct.Carrier middle u
  accounted : Accounted middle ledger [] [] u.wg
  extended : ∃ suffix, middle = history ++ suffix

structure EntryPath (item : Option (List SkbId)) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (v : World) (after : List CausalJournal.Event) : Prop where
  polled : ∃ pollLedger u middle, PollPath item w history pollLedger u middle ∧
    runPrefix (Driver.softirqObserved CausalJournal.hooks) u middle = (.ok ((),v),after)
  performed : runPrefix entryPrefix w history = (.ok (item,v),after)
  carrier : CompleteProduct.Carrier after v
  accounted : Accounted after ledger [] [] v.wg
  extended : ∃ suffix, after = history ++ suffix

theorem poll_path (before : CompleteProduct.Carrier history w)
    (performed : runPrefix CausalJournal.hooks.poll w history = (.ok (item,u),middle)) :
    ∃ ledger, PollPath item w history ledger u middle := by
  obtain ⟨suffix,grown,_,kept⟩ := CompleteProduct.poll w history before
  simp only [performed] at grown kept
  obtain ⟨ledger,accounted⟩ := kept.1
  exact ⟨ledger,performed,kept,accounted,⟨suffix,grown⟩⟩

theorem PollPath.entry (path : PollPath item w history pollLedger u middle)
    (performed : runPrefix (Driver.softirqObserved CausalJournal.hooks) u middle = (.ok ((),v),after)) :
    ∃ ledger, EntryPath item w history ledger v after := by
  obtain ⟨suffix,grown,_,kept⟩ := CompleteProduct.softirq u middle path.carrier
  simp only [performed] at grown kept
  obtain ⟨ledger,accounted⟩ := kept.1
  have actual : runPrefix entryPrefix w history = (.ok (item,v),after) := by
    rw [entryPrefix,runPrefix_bind,path.performed]
    change runPrefix (Driver.softirqObserved CausalJournal.hooks >>= fun _ => pure item) u middle = _
    rw [runPrefix_bind,performed]
    rfl
  obtain ⟨earlier,extended⟩ := path.extended
  exact ⟨ledger,⟨pollLedger,u,middle,path,performed⟩,actual,kept,accounted,
    ⟨earlier ++ suffix,by rw [grown,extended,List.append_assoc]⟩⟩

theorem EntryPath.iteration_run (path : EntryPath item w history ledger v after) :
    runPrefix (Driver.encryptIterObserved CausalJournal.hooks) w history = runPrefix (tail item) v after := by
  rw [iteration_factor,runPrefix_bind,path.performed]

inductive PrefixStop (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | poll (performed : runPrefix CausalJournal.hooks.poll w history = (.error reason,last))
      (safe : CompleteProduct.Safe last)
  | softirq (item : Option (List SkbId)) (ledger : Ledger) (u : World) (middle : List CausalJournal.Event)
      (path : PollPath item w history ledger u middle)
      (performed : runPrefix (Driver.softirqObserved CausalJournal.hooks) u middle = (.error reason,last))
      (safe : CompleteProduct.Safe last)

theorem PrefixStop.source_failed (stopped : PrefixStop w history reason last) :
    runPrefix entryPrefix w history = (.error reason,last) := by
  cases stopped with
  | poll performed _ => rw [entryPrefix,runPrefix_bind,performed]
  | softirq _ _ _ _ path performed _ =>
    rw [entryPrefix,runPrefix_bind,path.performed]
    change runPrefix (Driver.softirqObserved CausalJournal.hooks >>= fun _ => pure _) _ _ = _
    rw [runPrefix_bind,performed]

/-- Actual prefix case analysis, including Stops before the encryption
callback. The normal alternative retains both intermediate source runs. -/
theorem entry_cases (before : CompleteProduct.Carrier history w) :
    (∃ reason last, PrefixStop w history reason last) ∨
      ∃ item ledger v after, EntryPath item w history ledger v after := by
  cases polled : runPrefix CausalJournal.hooks.poll w history with
  | mk result middle =>
    cases result with
    | error reason =>
      obtain ⟨_,_,safe,_⟩ := CompleteProduct.poll w history before
      exact Or.inl ⟨reason,middle,.poll polled (by simpa only [polled] using safe)⟩
    | ok out =>
      obtain ⟨item,u⟩ := out
      obtain ⟨pollLedger,path⟩ := poll_path before polled
      cases handled : runPrefix (Driver.softirqObserved CausalJournal.hooks) u middle with
      | mk result after =>
        cases result with
        | error reason =>
          obtain ⟨_,_,safe,_⟩ := CompleteProduct.softirq u middle path.carrier
          exact Or.inl ⟨reason,after,.softirq item pollLedger u middle path handled
            (by simpa only [handled] using safe)⟩
        | ok out =>
          obtain ⟨value,v⟩ := out
          cases value
          obtain ⟨ledger,entry⟩ := path.entry handled
          exact Or.inr ⟨item,ledger,v,after,entry⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
