import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseSubmission

/-! The original entry derives semantic coverage of the entire fixed staging
tree. Neither a successful whole staging run nor a whole-tree certificate is
assumed. Allocation, create and queued-work primitive interiors have their
named child expansions; the canonical source points include later Stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging.Points
set_option maxHeartbeats 600000

theorem staging_covers (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    Covers (Evidence ledger debts locals) (stagingShape pid) w a h := by
  unfold stagingShape
  dsimp only [Covers]
  rw [covers_transport]
  apply covers_bind (selection_covers before (.refl _) pid a)
  intro choice u b middle selected
  cases choice with
  | none=>exact selection_normal_evidence before (.refl _) selected
  | some chosen=>
    obtain ⟨peer,key⟩:=chosen
    obtain ⟨after,generation,path,ready⟩:=Staging.Points.selected_entry before selected
    obtain ⟨r,_,_,_,_,_,assigned,_⟩:=path
    have steps : Staged.Obligations.Step ledger after:=assigned.symm ▸ transferLocation_step _ _ _
    have guarded:=allocation_prefix_covers key ready
    apply covers_bind (guarded.mono (fun _ _ _ kept=>.selected after steps kept))
    intro decision v c last performed
    have actual:=Staging.normal (Staging.allocation_checked after debts locals generation pid peer h.length key) ready performed
    cases decision with
    | unreachable=>exact invariant_covers (.selected after steps actual.1)
    | rejected key invalid=>exact rejected_covers key invalid actual.1 steps
    | submit kid packets=>exact submitted_covers actual.1 steps actual.2

/-- Every actual canonical point has a same-ledger semantic phase and the
literal original remainder, including points on a subsequently stopped run. -/
theorem staging_every_point (before : Accounted h ledger debts locals w)
    (point : Point (stagingShape pid) w a h leaf v b middle remaining) :
    Evidence ledger debts locals middle v b ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=runWGPrefix remaining v b middle :=
  ⟨(staging_covers before pid a).point point,point.residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
