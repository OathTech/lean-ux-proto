import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedTimerFrames

/-! Actual observed completion timer callbacks preserve one indexed semantic
entry. Native timer receipts may precede Stop; the retained frontier is the
same callback execution and cannot cross an unaccounted ledger event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity CompletionCuts

theorem ledger_quiet_birth (event : CausalJournal.Event) (quiet : ledgerEvent? event = none) :
    birthPackets event = [] := by
  cases event <;> try simp_all [ledgerEvent?,changesLedger,birthPackets]
  rename_i old
  cases old <;> simp_all

theorem ledger_history_birth_free (quiet : HistoryFrame ledgerEvent? action)
    (w : World) (history suffix : List CausalJournal.Event)
    (grown : (runPrefix action w history).2 = history ++ suffix) :
    ∀ event ∈ suffix, birthPackets event = [] := by
  have same := quiet w history
  rw [grown,List.filterMap_append] at same
  have empty : suffix.filterMap ledgerEvent? = [] :=
    List.append_cancel_left (as := history.filterMap ledgerEvent?)
      (by simpa only [List.append_nil] using same)
  exact fun event member => ledger_quiet_birth event (List.filterMap_eq_nil_iff.mp empty event member)

theorem discard_unit (action : PrefixM E Unit) : discard action = action := by
  have same : (fun _ : Unit => (pure () : PrefixM E Unit)) = pure := by
    funext value
    cases value
    rfl
  unfold discard
  rw [same,bind_pure]

theorem indexed_projected_checked (site : Site) (source : site.action = action)
    (appends : Appends action)
    (projected : ProjectsPrefix ledgerEvent? id action (liftPrefix (liftWG native)))
    (frame : SameView StagedEntry.view native) :
    Ensures (fun h w => Owned context phase h ledger debts w) (IndexedStopped context ledger debts)
      action (fun _ h w => Owned context phase h ledger debts w) := by
  have quiet : HistoryFrame ledgerEvent? action := fun w h => (congrArg Prod.snd (projected w h)).symm
  apply indexed_passive_checked site (source.trans (discard_unit action).symm) appends quiet
    (ledger_history_birth_free quiet)
  · intro w h
    have same := congrArg Prod.fst (projected w h)
    have eta : (fun x : Unit × World => (id x.1,x.2)) = id := by funext x; rfl
    simpa only [runPrefix_lift,eta,Except.map_id,id_eq] using same.symm
  · exact sameView_liftWG (fun w : World => StagedEntry.view w.wg) StagedEntry.view native frame
      (fun _ _ _ same => same)

private abbrev observedTimerOps := LifetimeEffects.decorate
  (CompletionEffects.lifetimeBase (CausalJournal.Event.old ∘ Journal.completionEvent)
    CausalJournal.completion?) CausalJournal.scope? CausalJournal.Event.armed CausalJournal.Event.queued

private theorem observed_timer_projects : LifetimeEffects.Ops.Projects ledgerEvent? observedTimerOps
    RawAppend.lifetimeLifted :=
  LifetimeEffects.decorate_projects ledgerEvent? _ _
    (RawAppend.lifetime_base_projects ledgerEvent? _ _ (fun _ => rfl))
    _ _ _ (fun _ => rfl) (fun _ => rfl)

theorem indexed_traversal_checked (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context phase h ledger debts w) (IndexedStopped context ledger debts)
      (CausalJournal.completionOps.traversal context.pid)
      (fun _ h w => Owned context phase h ledger debts w) := by
  apply indexed_projected_checked (native := timersTraversal context.pid)
    (.traversal context.pid) rfl (traversal_appends context.pid)
  · change ProjectsPrefix ledgerEvent? id
      (liftWGObserver (LifetimeEffects.traversalWith observedTimerOps context.pid))
      (liftPrefix (liftWG (timersTraversal context.pid)))
    have projected := (LifetimeEffects.traversal_projects ledgerEvent? observed_timer_projects context.pid).liftWGObserver ledgerEvent? id
    simpa only [RawAppend.lifetime_traversal,liftWGObserver_lift] using projected
  · exact traversal_entry_view context.pid

theorem indexed_dataSent_checked (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context phase h ledger debts w) (IndexedStopped context ledger debts)
      (CausalJournal.completionOps.dataSent context.pid)
      (fun _ h w => Owned context phase h ledger debts w) := by
  apply indexed_projected_checked (native := timersDataSent context.pid)
    (.dataSent context.pid) rfl (dataSent_appends context.pid)
  · change ProjectsPrefix ledgerEvent? id
      (liftWGObserver (LifetimeEffects.dataSentWith observedTimerOps context.pid))
      (liftPrefix (liftWG (timersDataSent context.pid)))
    have projected := (LifetimeEffects.dataSent_projects ledgerEvent? observed_timer_projects context.pid).liftWGObserver ledgerEvent? id
    simpa only [RawAppend.lifetime_dataSent,liftWGObserver_lift] using projected
  · exact dataSent_entry_view context.pid

theorem indexed_authenticated_checked (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context phase h ledger debts w) (IndexedStopped context ledger debts)
      (CausalJournal.completionOps.sent context.pid)
      (fun _ h w => Owned context phase h ledger debts w) := by
  have quiet : HistoryFrame ledgerEvent? (CausalJournal.completionOps.sent context.pid) := by
    change HistoryFrame ledgerEvent? (focusPrefix _ _ (Completion.access _))
    unfold Completion.access
    rw [CompletionEffects.focus_composed]
    exact focusPrefix_other _ _ _ (fun _ => rfl) _
  apply indexed_passive_checked (.authenticated context.pid)
    (show Site.action (.authenticated context.pid) = discard (CausalJournal.completionOps.sent context.pid)
      from (discard_unit _).symm)
    (Appends.focus _ _ _) quiet (ledger_history_birth_free quiet)
  · exact focusPrefix_erases _ _ (Completion.access_erases
      (timersAnyAuthenticatedPacketSentPrefix_erases context.pid))
  · exact sameView_liftWG (fun w : World => StagedEntry.view w.wg) StagedEntry.view _
      (authenticated_entry_view context.pid) (fun _ _ _ same => same)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
