import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointEntries

/-! Keepalive enters the same canonical staging tree after its own actual
preparation receipt. Insertion, queue reuse, refusal and stopped hidden
allocation retain distinct source cases and the precise birth position. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier
set_option maxHeartbeats 600000

noncomputable def keepalivePoint
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle)) :
    Point (keepaliveShape pid) w a h (Driver.stagingObserved hooks pid) u b middle
      (Driver.stagingObserved hooks pid) := by
  unfold keepaliveShape
  apply Point.marked
  exact .right (preparationShape pid) _ prepared (.entry (stagingShape pid))

/-- Actual preparation supplies the staging account on its exact successor
ledger; a true return alone is not mistaken for a new keepalive birth. -/
theorem keepalive_entry (before : Accounted h ledger debts locals w)
    (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle)) :
    let receipt : WGRunWitness Bool:=⟨true,w,u,a,b⟩
    middle=h++[.keepalivePrepared pid receipt] ∧
      receipt.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid) ∧
      ∃ after, Accounted middle after debts locals u ∧ KeepaliveChange h ledger pid receipt after :=
  CompleteKeepalive.normal pid before a b u middle true prepared

/-- Stops retain the actual preparation child; successful preparation keeps
the full same-ledger staging contract as the original continuation. -/
theorem keepalive_cases (before : Accounted h ledger debts locals w) :
    (∃ stop, StagingInterior.KeepaliveCase pid w a (.error stop) ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=(.error stop,h)) ∨
    (∃ ready u b after,
      let receipt : WGRunWitness Bool:=⟨ready,w,u,a,b⟩
      let middle:=h++[Event.keepalivePrepared pid receipt]
      StagingInterior.KeepaliveCase pid w a (.ok ((ready,u),b)) ∧
      Accounted middle after debts locals u ∧ KeepaliveChange h ledger pid receipt after ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=
        if ready then runWGPrefix (Driver.stagingObserved hooks pid) u b middle
        else (.ok (((),u),b),middle)) := by
  have paths:=StagingInterior.keepalive_cases pid w a
  cases native : ((RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error stop=>
    refine Or.inl ⟨stop,native ▸ paths,?_⟩
    change runWGPrefix (CausalJournal.keepalivePrepare pid >>= fun ready =>
      if ready then Driver.stagingObserved hooks pid else pure ()) w a h = _
    rw [run_bind,StagingInterior.keepalive_stopped native]
  | ok out=>
    obtain ⟨⟨ready,u⟩,b⟩:=out
    have prepared:=StagingInterior.keepalive_recorded (h:=h) native
    obtain ⟨_,_,after,accounted,change⟩:=CompleteKeepalive.normal pid before a b u _ ready prepared
    exact Or.inr ⟨ready,u,b,after,native ▸ paths,accounted,change,
      StagingInterior.keepalive_continuation native⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
