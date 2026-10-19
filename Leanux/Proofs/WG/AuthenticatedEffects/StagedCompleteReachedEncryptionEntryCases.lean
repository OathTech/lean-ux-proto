import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionEntryPath

/-! Failure classification for the actual encryption iteration. An encryption
callback failure keeps its exact entry and failed run; it does not assert an
unproved native cut inside that callback. The later reschedule branch keeps
the actual successful encryption output and its accounted ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompleteCarrier

inductive Stopped (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | early (stopped : PrefixStop w history reason last)
  | encrypt (item : Option (List SkbId)) (ledger : Ledger) (u : World) (middle : List CausalJournal.Event)
      (path : EntryPath item w history ledger u middle)
      (performed : runPrefix (CausalJournal.hooks.encrypt item) u middle = (.error reason,last))
      (safe : CompleteProduct.Safe last)
  | reschedule (item : Option (List SkbId)) (ledger : Ledger) (u : World) (middle : List CausalJournal.Event)
      (path : EntryPath item w history ledger u middle)
      (afterLedger : Ledger) (v : World) (after : List CausalJournal.Event)
      (encrypted : runPrefix (CausalJournal.hooks.encrypt item) u middle = (.ok (true,v),after))
      (carrier : CompleteProduct.Carrier after v)
      (accounted : Accounted after afterLedger [] [] v.wg)
      (performed : runPrefix (continuation true) v after = (.error reason,last))

theorem Stopped.source_failed (stopped : Stopped w history reason last) :
    runPrefix (Driver.encryptIterObserved CausalJournal.hooks) w history = (.error reason,last) := by
  cases stopped with
  | early stopped => rw [iteration_factor,runPrefix_bind,stopped.source_failed]
  | encrypt _ _ _ _ path performed _ => rw [path.iteration_run,tail,runPrefix_bind,performed]
  | reschedule _ _ _ _ path _ _ _ encrypted _ _ performed =>
    rw [path.iteration_run,tail,runPrefix_bind,encrypted]
    exact performed

/-- All callbacks are the concrete final-journal sources. Every stopped
alternative keeps the native input and original continuation that selected it. -/
theorem iteration_failed (before : CompleteProduct.Carrier history w)
    (failed : runPrefix (Driver.encryptIterObserved CausalJournal.hooks) w history = (.error reason,last)) :
    Stopped w history reason last := by
  rcases entry_cases before with early | entered
  · obtain ⟨stop,after,stopped⟩ := early
    have native := stopped.source_failed
    rw [iteration_factor,runPrefix_bind,native] at failed
    cases failed
    exact .early stopped
  · obtain ⟨item,ledger,u,middle,path⟩ := entered
    rw [path.iteration_run,tail,runPrefix_bind] at failed
    cases encrypted : runPrefix (CausalJournal.hooks.encrypt item) u middle with
    | mk outcome after =>
      rw [encrypted] at failed
      obtain ⟨_,_,safe,kept⟩ := CompleteProduct.encrypt item u middle path.carrier
      simp only [encrypted] at safe kept
      cases outcome with
      | error stop =>
        cases failed
        exact .encrypt item ledger u middle path encrypted safe
      | ok out =>
        obtain ⟨more,v⟩ := out
        obtain ⟨afterLedger,accounted⟩ := kept.1
        cases more with
        | false => simp only [continuation,Bool.not_false,↓reduceIte,runPrefix_pure] at failed; cases failed
        | true => exact .reschedule item ledger u middle path afterLedger v after encrypted kept accounted failed

def afterEncryptPrefix : PrefixM CausalJournal.Event Bool := do
  let item ← entryPrefix
  CausalJournal.hooks.encrypt item

theorem EntryPath.after_encrypt (path : EntryPath item w history ledger u middle)
    (encrypted : runPrefix (CausalJournal.hooks.encrypt item) u middle = (.ok (more,v),after)) :
    runPrefix afterEncryptPrefix w history = (.ok (more,v),after) := by
  rw [afterEncryptPrefix,runPrefix_bind,path.performed]
  exact encrypted

theorem continuation_history (more : Bool) (w : World) (history : List CausalJournal.Event) :
    (runPrefix (continuation more) w history).2 = history := by
  have unchanged : (runPrefix (Driver.reschedObserved .encryptWorker .encWorkerNeedResched) w history).2 = history := by
    unfold Driver.reschedObserved
    rw [runPrefix_bind,runPrefix_lift]
    cases (Env.condResched .encryptWorker).run w <;> rfl
  cases more with
  | false => rfl
  | true =>
    simp only [continuation,Bool.not_true,Bool.false_eq_true,↓reduceIte,runPrefix_bind]
    cases performed : runPrefix (Driver.reschedObserved .encryptWorker .encWorkerNeedResched) w history with
    | mk outcome after =>
      rw [performed] at unchanged
      cases outcome <;> exact unchanged

theorem reschedule_cut (path : EntryPath item w history ledger u middle)
    (encrypted : runPrefix (CausalJournal.hooks.encrypt item) u middle = (.ok (true,v),after))
    (accounted : Accounted after afterLedger [] [] v.wg)
    (failed : runPrefix (continuation true) v after = (.error reason,last)) :
    runPrefix afterEncryptPrefix w history = (.ok (true,v),after) ∧
      last = after ∧ Accounted last afterLedger [] [] v.wg := by
  have same : last = after := by simpa only [failed] using continuation_history true v after
  exact ⟨path.after_encrypt encrypted,same,by simpa only [same] using accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionEntry
