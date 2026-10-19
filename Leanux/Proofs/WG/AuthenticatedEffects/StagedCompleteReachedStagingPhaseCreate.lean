import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseModel

/-! The canonical create certificate is instantiated at the actual staged
allocator call. Its unpublished account and batch are derived from the same
selection and guard runs; no independent create-entry premise is supplied. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier AllocatedObligation Staging
set_option maxHeartbeats 600000

theorem create_certificate
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,v),c),last)) :
    ∃ after generation items q,
      let receipt : WGRunWitness (List SkbId):=⟨items,v,q,c,c⟩
      let events:=last++[Event.old (.allocated packets receipt)]
      let assigned:=assignBatch h.length last.length after
      Staged.Obligations.Step ledger assigned ∧
      CallbackPath h ledger debts locals pid w a peer key middle u b after generation (.submit kid packets) last v c ∧
      runWGPrefix (state (Journal.allocate packets)) v c last=(.ok ((items,q),c),events) ∧
      Accounted events assigned debts (⟨.unpublished,pid,items⟩::locals) q ∧
      CreateDisposal.PendingBatch events assigned items ∧
      CreatePhase.Covers (fun events world=>CreatePhase.Live assigned debts locals pid items events world.wg)
        (CreatePoints.createShape pid items) (NativeAdapter.world q c) events ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=runWGPrefix (CausalJournal.create pid items) q c events := by
  obtain ⟨after,generation,path⟩:=Staging.Points.callback_entry before selected guarded
  obtain ⟨items,q,performed,_,assignedStep,accounted,pending,_⟩:=Allocation.allocate_intervals path.ready path.shape
  have fromEntry : Staged.Obligations.Step ledger after := by
    obtain ⟨r,_,_,_,_,_,transferred,_⟩:=path.selected
    rw [transferred]
    exact transferLocation_step _ _ _
  refine ⟨after,generation,items,q,fromEntry.trans assignedStep,path,performed,accounted,pending,?_,?_⟩
  · exact CreatePhase.create_covers pending accounted
  · exact (Staging.Points.createPoint selected guarded performed).residual

/-- This joins any actual child point back to the literal original staging
continuation, including if that continuation subsequently stops. -/
theorem create_every_point
    (before : Accounted h ledger debts locals w)
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,v),c),last))
    (allocated : runWGPrefix (state (Journal.allocate packets)) v c last=(.ok ((items,q),d),events))
    (point : CreatePoints.Point (CreatePoints.createShape pid items) (NativeAdapter.world q d) events
      leaf current history remaining) :
    ∃ assigned,Staged.Obligations.Step ledger assigned ∧ CreatePhase.Evidence assigned debts locals pid items history current ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a h=
        ((runPrefix remaining current history).1.map (fun (value,world)=>((value,world.wg),world.ambient)),
          (runPrefix remaining current history).2) := by
  obtain ⟨after,generation,ids,world,steps,path,performed,accounted,pending,certificate,_⟩:=
    create_certificate before selected guarded
  rw [allocated] at performed
  cases performed
  refine ⟨assignBatch h.length last.length after,steps,.live (certificate.point point),?_⟩
  exact (Staging.Points.createPoint selected guarded allocated).residual.trans point.lowered

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
