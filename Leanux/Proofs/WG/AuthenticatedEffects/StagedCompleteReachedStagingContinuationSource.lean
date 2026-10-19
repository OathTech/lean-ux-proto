import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCompositionAllCreation

/-! Source-only continuations for staging's allocator and product-observer
creation child. Projection keeps the exact captured non-WG fields of the
child cut; it introduces no native state or observation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingContinuation
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging Staging.Points StagingComposition StagingPrimitive

def lowerAt (saved : World) (body : PrefixM Event α) : WGPrefix Event α :=
  fun wg ambient=>ExceptT.mk fun h=>
    let out:=runPrefix body {saved with wg,ambient} h
    (out.1.map (fun (value,w)=>((value,w.wg),w.ambient)),out.2)

theorem lower_at_run (saved : World) (body : PrefixM Event α) :
    runWGPrefix (lowerAt saved body) saved.wg saved.ambient h=
      ((runPrefix body saved h).1.map (fun (value,w)=>((value,w.wg),w.ambient)),
        (runPrefix body saved h).2) := rfl

theorem allocate_residual (device : w.dev=some d)
    (path : Allocation.Path packets w a n items v) :
    runWGPrefix (state (Journal.allocate packets)) w a h=
      runWGPrefix (Allocation.remainder packets n items w a) v a h := by
  obtain ⟨allItems,target,_,_,native⟩:=Staged.Obligations.HeldFrontier.allocate_total packets w a device
  obtain ⟨rest,remaining,ordered⟩:=path.remaining native
  rw [Staged.Obligations.HeldFrontier.allocation_observed packets w target a a allItems native h]
  simp [Allocation.remainder,Staging.Points.savedReceipt,runWGPrefix_receiptWGObserved,
    runWGPrefix_lift,remaining,ordered]

theorem create_residual
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (Staging.allocationPrefix pid peer key) u b middle=
      (.ok ((.submit kid packets,q),c),events))
    (allocated : runWGPrefix (state (Journal.allocate packets)) q c events=(.ok ((items,t),e),prior))
    (point : CreateExpanded.Point pid items (NativeAdapter.world t e) prior v last) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a h=
      runWGPrefix (lowerAt v (CreateExpanded.remainder point)) v.wg v.ambient last := by
  rw [lower_at_run,(Staging.Points.createPoint selected guarded allocated).residual,
    CreatePoints.lower_factor,runWGPrefix,NativeAdapter.run_lower,CreateExpanded.remainder_run point]

theorem reserve_residual
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (call : Call (allocationPrefixShape pid peer key) u b middle (.reserve slot) q c events context)
    (point : ReservePoint slot q c events v d last rest) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a h=
      runWGPrefix (context rest >>= allocationTail pid peer) v d last := by
  rw [(selectedPoint selected).residual,run_bind,run_bind,call.resume point.residual]

theorem repayment_residual
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.rejected rejectedKey invalid,q),c),events))
    (call : Call (rejectPrefixShape peer.staged rejectedKey invalid) q c events (.repayment repayKey) t e prior context)
    (point : KeyPoint (keyShape repayKey) t e leaf v d rest) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a h=
      runWGPrefix (context (liftWGPrefix rest) >>= fun _=>rejectedTail pid peer) v d prior := by
  have original:=(callbackPoint selected guarded).residual
  change runWGPrefix (Driver.stagingObserved hooks pid) w a h=
    runWGPrefix (HeldSource.noKey pid peer rejectedKey invalid) q c events at original
  rw [rejection_factor] at original
  have child : runWGPrefix (liftWGPrefix (keypairPut repayKey false)) t e prior=
      runWGPrefix (liftWGPrefix rest) v d prior := by
    rw [runWGPrefix_lift,runWGPrefix_lift,point.residual]
  rw [original,run_bind,run_bind,call.resume child]

theorem queued_residual
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.rejected rejectedKey invalid,q),c),events))
    (prefixRun : runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged rejectedKey invalid)
      q c events=(.ok (((),t),e),prior))
    (restoreRun : runWGPrefix (CausalJournal.stagedRestore pid peer.staged) t e prior=(.ok (((),restored),clock),recorded))
    (point : QueuePoint pid restored clock recorded v d last rest) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a h=runWGPrefix rest v d last := by
  have original:=(callbackPoint selected guarded).residual
  change runWGPrefix (Driver.stagingObserved hooks pid) w a h=
    runWGPrefix (HeldSource.noKey pid peer rejectedKey invalid) q c events at original
  rw [rejection_factor,run_bind,prefixRun] at original
  dsimp only at original
  unfold rejectedTail at original
  rw [run_bind,restoreRun] at original
  exact original.trans point.residual

theorem allocation_residual
    (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
    (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,q),c),events))
    (device : q.dev=some d) (path : Allocation.Path packets q c count items v) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a h=
      runWGPrefix (Allocation.remainder packets count items q c >>= CausalJournal.create pid) v c events := by
  rw [(callbackPoint selected guarded).residual]
  change runWGPrefix (state (Journal.allocate packets) >>= CausalJournal.create pid) q c events=_
  rw [run_bind,run_bind,allocate_residual device path]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingContinuation
