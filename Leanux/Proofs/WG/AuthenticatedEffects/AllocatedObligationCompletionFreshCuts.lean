import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFreshPrefixes

/-! Exact indexed entry transport for completion's access prefixes and its
paired repayment. The latter is total and nonfinal from the actual borrow;
its receipt remains present even though the fixed ledger is unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal TransmitSecurity.Staged.Obligations

theorem prefix_returned {action : WGPrefix CausalJournal.Event α} {native : WG.M α}
    (appends : StateAppends action)
    (projected : StateProjectsPrefix ledgerEvent? id action (liftWGPrefix native))
    (frame : SameView StagedEntry.view native)
    (before : Owned context phase history ledger debts w)
    (performed : runPrefix (liftWGObserver action) w history = (.ok (value,v),last)) :
    (liftWG native).run w = .ok (value,v) ∧
      Owned context phase last ledger debts v ∧
      last.filterMap ledgerEvent? = history.filterMap ledgerEvent? := by
  obtain ⟨erases,quiet⟩ := projected_parts projected
  have nativeRun := (liftWGObserver_erases erases w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,grown⟩ := appends.liftWGObserver w history
  have free := ledger_history_birth_free quiet.liftWGObserver w history suffix grown
  have kept := before.same_view ((ProjectedAction.iff_run _ _ _).mp
    (sameView_liftWG (fun w : World => StagedEntry.view w.wg) StagedEntry.view native frame
      (fun _ _ _ same => same)) w value v nativeRun)
  rw [performed] at grown
  change last = history ++ suffix at grown
  exact ⟨nativeRun,(by simpa only [grown] using kept.append suffix free),
    (by simpa only [performed] using quiet.liftWGObserver w history)⟩

theorem prefix_failed {action : WGPrefix CausalJournal.Event α} {native : WG.M α}
    (projected : StateProjectsPrefix ledgerEvent? id action (liftWGPrefix native))
    (performed : runPrefix (liftWGObserver action) w history = (.error reason,last)) :
    last.filterMap ledgerEvent? = history.filterMap ledgerEvent? := by
  have quiet := (projected_parts projected).2.liftWGObserver w history
  simpa only [performed] using quiet

/-- A strict borrow in this same invocation supplies the reference which
the native nested callback repays. No ambient funding assumption is used by
the queued caller; that caller derives this precise condition from its prefix. -/
theorem repayment_total (pid : PeerId)
    (before : Owned context phase history ledger debts w)
    (funded : StagedEntry.Queued.Funded pid w.wg) :
    ∃ g a suffix,
      ((releaseCut (some pid)).run w.wg).run w.ambient = .ok ((none,g),a) ∧
      runPrefix (liftWGObserver (CausalJournal.completionLifetime.put (some pid))) w history =
        (.ok ((),{w with wg := g,ambient := a}),
          (history ++ suffix) ++ [PeerRelease.receipt (some pid) none w.wg g w.ambient a]) ∧
      Owned context phase ((history ++ suffix) ++
        [PeerRelease.receipt (some pid) none w.wg g w.ambient a]) ledger debts
        {w with wg := g,ambient := a} := by
  obtain ⟨g,a,native⟩ := Publication.release_cut_nonfinal pid funded w.ambient
  obtain ⟨suffix,grown,_⟩ := PeerRelease.cut_birth_quiet (some pid) w.wg w.ambient history
  have result := PeerRelease.cut_erases (some pid) w.wg w.ambient history
  have cutRun : runWGPrefix (PeerRelease.cut (some pid)) w.wg w.ambient history =
      (.ok ((none,g),a),history ++ suffix) := Prod.ext (result.trans native) grown
  obtain ⟨after,_,_,same,owned⟩ := indexed_release_cut (some pid) before cutRun
  change after = ledger at same
  subst after
  refine ⟨g,a,suffix,native,?_,owned⟩
  rw [put_actual,PeerRelease.after_cut (some pid) cutRun]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
