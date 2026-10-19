import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionLoop
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteDispose
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalNested

/-! Ordinary cleanup has no new first-terminal demand. The actual later peer
release may settle staged tickets, so its prefixes use the counted-release
contract rather than treating the complete disposal suffix as quiet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedDisposal
variable {Safe : List CausalJournal.Event → Prop}

private abbrev disposeOps := TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
  CausalJournal.Event.stagedDisposal

theorem free_loop_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context (.freeing remaining) history ledger debts w)
    (localDebts : LocalDebts context remaining debts) (complete : Complete history ledger) :
    ∃ v suffix, runPrefix (freeLoop disposeOps remaining) w history = (.ok ((),v),history ++ suffix) ∧
      Owned context (.freeing []) (history ++ suffix) ledger [] v ∧
      Complete (history ++ suffix) ledger ∧ Cuts Safe history suffix := by
  obtain ⟨v,suffix,source,after,paired⟩ := Converse.freeLoop_total remaining before localDebts complete
  have quiet := Converse.freeLoop_quiet remaining w history
  rw [source] at quiet
  exact ⟨v,suffix,source,after,paired,quiet_cuts accountSafe before complete quiet⟩

theorem dispose_cuts (key : KeypairId) (accountSafe : AccountSafe Safe)
    (before : Owned context (.freeing context.items) history ledger debts w)
    (localDebts : LocalDebts context context.items debts) (complete : Complete history ledger) :
    ∃ suffix, (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w history).2 =
      history ++ suffix ∧ Cuts Safe history suffix := by
  obtain ⟨freeWorld,freeSuffix,freed,atFree,freeComplete,freeCuts⟩ := free_loop_cuts accountSafe before localDebts complete
  change ∃ suffix, (runPrefix (TxSource.dispose disposeOps context.pid context.items key) w history).2 =
    history ++ suffix ∧ Cuts Safe history suffix
  rw [← dispose_factor]
  simp only [dispose,release,runPrefix_bind,freed]
  have keyQuiet : HistoryFrame ledgerEvent? (disposeOps.access (keypairPutPrefix (some key) false)) :=
    focusPrefix_other _ _ _ (fun _ => rfl) _
  obtain ⟨keySuffix,keyGrown,keyCuts⟩ := quiet_output accountSafe atFree freeComplete (Appends.focus _ _ _) keyQuiet
  change (runPrefix (disposeOps.access (keypairPutPrefix (some key) false)) freeWorld (history ++ freeSuffix)).2 = _ at keyGrown
  obtain ⟨_,_,keyChecked⟩ := indexed_keyRelease_checked context key (.freeing []) ledger []
    freeWorld (history ++ freeSuffix) atFree
  have keyComplete := Converse.history_preserved freeComplete (Appends.focus _ _ _) keyQuiet (w := freeWorld)
  change Complete (runPrefix (disposeOps.access (keypairPutPrefix (some key) false)) freeWorld (history ++ freeSuffix)).2 ledger at keyComplete
  cases paid : runPrefix (disposeOps.access (keypairPutPrefix (some key) false)) freeWorld (history ++ freeSuffix) with
  | mk outcome keyHistory =>
    rw [paid] at keyGrown keyChecked keyComplete
    change keyHistory = (history ++ freeSuffix) ++ keySuffix at keyGrown
    cases outcome with
    | error reason =>
      exact ⟨freeSuffix ++ keySuffix,by simpa only [List.append_assoc] using keyGrown,
        freeCuts.append keyCuts⟩
    | ok out =>
      obtain ⟨ignored,keyWorld⟩ := out
      cases ignored
      dsimp only
      obtain ⟨peerSuffix,peerGrown,peerCuts⟩ := Disposal.nested_cuts (some context.pid) Safe
        (fun l h g => accountSafe h l [] _ g) keyWorld keyHistory
        ⟨ledger,keyChecked.entry,keyComplete⟩
      change (runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory).2 = keyHistory ++ peerSuffix at peerGrown
      have combined := (freeCuts.append keyCuts).append (by
        simpa only [keyGrown,List.append_assoc] using peerCuts)
      refine ⟨(freeSuffix ++ keySuffix) ++ peerSuffix,?_,combined⟩
      cases repaid : runPrefix (disposeOps.release (some context.pid)) keyWorld keyHistory with
      | mk outcome last =>
        rw [repaid] at peerGrown
        cases outcome with
        | error reason => simpa only [keyGrown,List.append_assoc] using peerGrown
        | ok result => cases result.1; simpa only [runPrefix_pure,keyGrown,List.append_assoc] using peerGrown

theorem dispose (context : Context) (key : KeypairId) (ledger : Ledger) (debts : List CleanupDebt)
    (accountSafe : AccountSafe Safe) :
    Checked (fun h w => Owned context (.freeing context.items) h ledger debts w ∧
      LocalDebts context context.items debts ∧ Complete h ledger)
      Safe (Converse.DisposeStopped context key ledger)
      (CausalJournal.completionOps.dispose context.pid context.items key)
      (fun value h w => Converse.DisposeReturned context ledger h value w) := by
  apply Checked.of_cuts
  · intro w h before
    obtain ⟨_,_,_,_,_,result⟩ := Converse.dispose_cases key before.1 before.2.1 before.2.2
    obtain ⟨suffix,grown,_⟩ := dispose_cuts key accountSafe before.1 before.2.1 before.2.2
    refine ⟨suffix,grown,?_⟩
    cases run : (runPrefix (CausalJournal.completionOps.dispose context.pid context.items key) w h).1 with
    | error reason => simpa only [run] using result
    | ok out => obtain ⟨value,v⟩ := out; simpa only [run] using result
  · intro w h before
    exact dispose_cuts key accountSafe before.1 before.2.1 before.2.2

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
