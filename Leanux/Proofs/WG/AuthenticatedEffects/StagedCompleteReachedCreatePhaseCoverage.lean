import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseTail

/-! Original unpublished ownership derives a semantic certificate for the
fixed canonical create tree. The theorem covers each actual source Point,
including prefixes of later Stops; primitive child interiors remain explicit
and erased-cell subpoints have their separate pending-receipt evidence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

theorem create_covers (pending : PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    Covers (fun h w=>Live ledger debts locals pid items h w.wg) (createShape pid items) w h := by
  cases items with
  | nil=>exact atom_covers (.fault Unit .empty) trivial (.unpublished ledger (.refl _) pending before)
  | cons first rest=>
    unfold createShape
    apply covers_marked
    dsimp only [id]
    erw [covers_type_cast _ (Admission.final_factor pid (first::rest)).symm]
    dsimp only [List.head?]
    have frontSafe:=front_covers (.refl ledger) pending before
    apply covers_bind frontSafe
    intro ret u middle admitted
    obtain ⟨suffix,grown⟩:=Admission.actual_appends pid (first::rest) w h
    rw [admitted] at grown
    change middle=h++suffix at grown
    have batch : PendingBatch middle ledger (first::rest) := grown ▸ pending.append suffix
    have result:=CompleteSource.admission_cases pid (first::rest) before
    rw [admitted] at result
    rcases result.2 with ⟨code,entry⟩ | ⟨code,entry⟩
    · exact tail_unpublished first ret (.refl _) batch entry
    · exact tail_accepted first ret code (frontSafe.normal admitted)

/-- Every canonical point has semantic ownership on a successor of the SAME
entry ledger and retains the literal original remaining computation. This is
source-local, not an initialized or primitive-internal coverage theorem. -/
theorem every_point (pending : PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (point : Point (createShape pid items) w h leaf u middle remaining) :
    Evidence ledger debts locals pid items middle u ∧
      runPrefix (body pid items) w h=runPrefix remaining u middle :=
  ⟨.live ((create_covers pending before).point point),point.residual⟩

theorem point_accounted (pending : PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (point : Point (createShape pid items) w h leaf u middle remaining) :
    ∃ current active,Staged.Obligations.Step ledger current ∧ Accounted middle current debts active u.wg :=
  ((create_covers pending before).point point).accounted

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
