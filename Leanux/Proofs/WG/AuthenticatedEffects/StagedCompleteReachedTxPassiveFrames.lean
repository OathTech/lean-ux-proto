import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxPassiveSource

/-! Completion prefixes preserve the selected account and its settlement
chain. The actual source run chooses the cut; accounting does not choose it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxPassive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompleteCarrier Staged.Obligations CompletionCuts
variable {initial : Ledger}

theorem prelude_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) (stage : PreludeStage) :
    CompletionCuts.Ensures (Converse.Sending context initial original context.items) (Converse.SendingStopped context initial original)
      (preludeLeading context.pid context.items stage) (fun _=>Converse.Sending context initial original context.items) := by
  have marker:=Converse.sending_passive context initial original context.items _ (indexed_marker_checked context)
    (fun _ _ w complete=>Converse.marker_complete context.pid context.items complete w)
  have traversal:=Converse.sending_passive context initial original context.items _
    (indexed_traversal_checked context (.sending context.items))
    (fun _ _ w complete=>Converse.traversal_complete context.pid complete w)
  cases stage with
  | start=>exact CompletionCuts.Ensures.pure (fun _ _ h=>h)
  | marked=>exact marker
  | traversed=>exact CompletionCuts.Ensures.bind marker (fun _=>traversal)
  | prepared=>exact Sending.prelude_checked context initial original

theorem guard_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) (sent : Bool) :
    CompletionCuts.Ensures (Converse.Sending context initial original []) (Converse.SendingStopped context initial original)
      (Completion.finishGuard sent) (fun _=>Converse.Sending context initial original []) :=
  CompletionCuts.Ensures.bind (Converse.sending_choice context initial original [] _ _)
    (fun _=>Converse.sending_choice context initial original [] _ _)

theorem data_checked (context : Context) (initial : Ledger) (original : List CleanupDebt) (flag : Bool) :
    CompletionCuts.Ensures (Converse.Sending context initial original []) (Converse.SendingStopped context initial original)
      (data context.pid flag) (fun _=>Converse.Sending context initial original []) := by
  cases flag with
  | false=>exact CompletionCuts.Ensures.pure (fun _ _ h=>h)
  | true=>
      exact Converse.sending_passive context initial original [] _ (indexed_dataSent_checked context (.sending []))
        (fun _ _ w complete=>Converse.dataSent_complete context.pid complete w)

theorem finish_checked (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (sent : Bool) (stage : FinishStage) :
    CompletionCuts.Ensures (Converse.Sending context initial original []) (Converse.SendingStopped context initial original)
      (finishLeading context.pid sent stage) (fun _=>Converse.Sending context initial original []) := by
  cases stage with
  | start=>exact CompletionCuts.Ensures.pure (fun _ _ h=>h)
  | guarded=>exact guard_checked context initial original sent
  | data=>exact CompletionCuts.Ensures.bind (guard_checked context initial original sent) (fun flag=>
      CompletionCuts.Ensures.bind (data_checked context initial original flag) (fun _=>CompletionCuts.Ensures.pure (fun _ _ h=>h)))
  | fresh=>exact CompletionCuts.Ensures.bind (guard_checked context initial original sent) (fun flag=>
      CompletionCuts.Ensures.bind (data_checked context initial original flag) (fun _=>
        CompletionCuts.Ensures.bind (Converse.sending_fresh context initial original []) (fun _=>CompletionCuts.Ensures.pure (fun _ _ h=>h))))

theorem prelude_sending (before : Accounted h initial [] locals w.wg)
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (performed : runPrefix (preludeLeading pid items stage) u
      (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last)) :
    TxSending.Evidence initial locals pid last v := by
  have selection:=selection_returned before selected
  obtain ⟨account,pending⟩:=selection.accounted_entry
  obtain ⟨context,peer,localEq,batch,_,_,owned⟩:=TxSelection.selected_context account.entry pending
  have atEntry:=Converse.Sending.start owned (LocalDebts.empty context context.items) account.complete
  have atScope:=atEntry.append [WorkerCompletion.entered pid items middle]
    (by intro event member; cases List.mem_singleton.mp member; rfl)
    (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  obtain ⟨_,_,checked⟩:=prelude_checked context initial [] stage u _ atScope
  rw [peer,batch,performed] at checked
  exact TxSending.sending_evidence peer localEq checked

theorem finish_sending (before : Accounted h initial [] locals w.wg)
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (prepared : runPrefix (WorkerCompletion.prelude pid items) u
      (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last))
    (looped : runPrefix (sendLoop CausalJournal.completionOps pid items false) v last=(.ok (sent,q),after))
    (performed : runPrefix (finishLeading pid sent stage) q after=(.ok (flag,r),events)) :
    TxSending.Evidence initial locals pid events r := by
  obtain ⟨context,peer,localEq,_,_,sending⟩:=
    TxSending.loop_sending before selected prepared (List.append_nil items).symm looped
  obtain ⟨_,_,checked⟩:=finish_checked context initial [] sent stage q after sending
  rw [peer,performed] at checked
  exact TxSending.sending_evidence peer localEq checked

/-- Security: completion markers and timer/rekey callbacks preserve the
selected batch and the same settlement chain. Successful prelude and finish
prefixes cannot create, lose or settle a packet ticket. -/
theorem Point.evidence (before : Accounted h initial [] locals w.wg)
    (point : Point pid w h u middle) : TxSending.Evidence initial locals pid middle u := by
  cases point with
  | prelude selected performed=>exact prelude_sending before selected performed
  | finish selected prepared looped performed=>exact finish_sending before selected prepared looped performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxPassive
