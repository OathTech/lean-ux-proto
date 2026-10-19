import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteCleanup

/-! Completion bookkeeping and timer receipts preserve terminal completeness
through their exact source projections. The property is paired with the same
indexed ownership ledger, including the actual stopped callback frontier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompletionCuts

theorem state_prefix_complete
    (appends : StateAppends action)
    (projected : StateProjectsPrefix ledgerEvent? id action (liftWGPrefix native))
    (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (liftWGObserver action) w history).2 ledger :=
  history_preserved complete appends.liftWGObserver (Fresh.projected_parts projected).2.liftWGObserver

theorem marker_complete (pid : PeerId) (items : List SkbId)
    (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (CausalJournal.completionOps.completion pid items) w history).2 ledger := by
  have run : runPrefix (CausalJournal.completionOps.completion pid items) w history =
      (.ok ((),w),history ++ [.old (.disposition (.completion pid items))]) :=
    focusPrefix_suffix FirstTerminal.encode CausalJournal.completion?
      (emitPrefix (.disposition (.completion pid items))) w history (.ok ((),w))
      [.disposition (.completion pid items)] (runPrefix_emit _ w _)
  rw [run]
  apply complete.append_quiet
  intro event member
  cases List.mem_singleton.mp member
  intro position
  rfl

theorem traversal_complete (pid : PeerId) (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (CausalJournal.completionOps.traversal pid) w history).2 ledger := by
  have projected := (LifetimeEffects.traversal_projects ledgerEvent? Fresh.prefix_projects pid).liftWGObserver ledgerEvent? id
  have quiet : HistoryFrame ledgerEvent? (CausalJournal.completionOps.traversal pid) := by
    change HistoryFrame ledgerEvent? (liftWGObserver (LifetimeEffects.traversalWith Fresh.prefixOps pid))
    intro v events
    have same := congrArg Prod.snd (projected v events)
    simpa only [RawAppend.lifetime_traversal,liftWGObserver_lift,runPrefix_lift] using same.symm
  exact history_preserved complete (traversal_appends pid) quiet

theorem dataSent_complete (pid : PeerId) (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (CausalJournal.completionOps.dataSent pid) w history).2 ledger := by
  have projected := (LifetimeEffects.dataSent_projects ledgerEvent? Fresh.prefix_projects pid).liftWGObserver ledgerEvent? id
  have quiet : HistoryFrame ledgerEvent? (CausalJournal.completionOps.dataSent pid) := by
    change HistoryFrame ledgerEvent? (liftWGObserver (LifetimeEffects.dataSentWith Fresh.prefixOps pid))
    intro v events
    have same := congrArg Prod.snd (projected v events)
    simpa only [RawAppend.lifetime_dataSent,liftWGObserver_lift,runPrefix_lift] using same.symm
  exact history_preserved complete (dataSent_appends pid) quiet

theorem authenticated_complete (pid : PeerId) (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (CausalJournal.completionOps.sent pid) w history).2 ledger :=
  focused_access_complete complete (timersAnyAuthenticatedPacketSentPrefix pid) w

theorem sending_passive (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (action : PrefixM CausalJournal.Event α)
    (checked : ∀ ledger debts,
      Ensures (fun h w => Owned context (.sending remaining) h ledger debts w)
        (IndexedStopped context ledger debts) action
        (fun _ h w => Owned context (.sending remaining) h ledger debts w))
    (preserves : ∀ ledger h w, Complete h ledger → Complete (runPrefix action w h).2 ledger) :
    Ensures (Sending context initial original remaining) (SendingStopped context initial original)
      action (fun _ => Sending context initial original remaining) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before
  obtain ⟨suffix,grown,result⟩ := checked ledger debts w history owned
  have paired := preserves ledger history w complete
  refine ⟨suffix,grown,?_⟩
  cases run : (runPrefix action w history).1 with
  | error reason => exact ⟨ledger,debts,trace,(by simpa only [run] using result),paired⟩
  | ok out => exact ⟨ledger,debts,trace,(by simpa only [run] using result),localDebts,paired⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
