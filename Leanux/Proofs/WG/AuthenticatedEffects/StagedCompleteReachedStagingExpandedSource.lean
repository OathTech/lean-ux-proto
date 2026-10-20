import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingContinuationSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAllocationNativeContinuation

/-! The staging source family includes each previously proved deeper child.
Every constructor retains the original selection/guard calls and the fixed
child witness; none accepts an extensional factorization as provenance. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingExpanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging Staging.Points StagingComposition StagingPrimitive

inductive Point (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    WGWorld → Ambient → List Event → Prop where
  | canonical (point : Staging.Points.Point (stagingShape pid) w a h leaf v b last remaining) :
      Point pid w a h v b last
  | reserve
      (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
      (call : Call (allocationPrefixShape pid peer key) u b middle (.reserve slot) q c events context)
      (point : ReservePoint slot q c events v d last rest) : Point pid w a h v d last
  | repayment
      (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
      (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.rejected rejectedKey invalid,q),c),events))
      (call : Call (rejectPrefixShape peer.staged rejectedKey invalid) q c events (.repayment repayKey) t e prior context)
      (point : KeyPoint (keyShape repayKey) t e leaf v d rest) : Point pid w a h v d prior
  | queued
      (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
      (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.rejected rejectedKey invalid,q),c),events))
      (prefixRun : runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged rejectedKey invalid)
        q c events=(.ok (((),t),e),prior))
      (restoreRun : runWGPrefix (CausalJournal.stagedRestore pid peer.staged) t e prior=(.ok (((),restored),clock),recorded))
      (point : QueuePoint pid restored clock recorded v d last rest) : Point pid w a h v d last
  | allocation
      (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
      (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,q),c),events))
      (device : q.dev=some d) (path : Allocation.Path packets q c count items v) : Point pid w a h v c events
  | allocationNative
      (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
      (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,q),c),events))
      (device : q.dev=some d) (point : Allocation.Point packets q c v e) : Point pid w a h v e events
  | creation
      (selected : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((some (peer,key),u),b),middle))
      (guarded : runWGPrefix (allocationPrefix pid peer key) u b middle=(.ok ((.submit kid packets,q),c),events))
      (allocated : runWGPrefix (state (Journal.allocate packets)) q c events=(.ok ((items,t),e),prior))
      (point : CreateExpanded.Point pid items (NativeAdapter.world t e) prior v last) :
      Point pid w a h v.wg v.ambient last

/-- Every declared native staging cut retains the literal remainder of the
same invocation, independently of the accounting theorem or normal return. -/
theorem Point.residual (point : Point pid w a h v b last) :
    ∃remaining,runWGPrefix (Driver.stagingObserved hooks pid) w a h=runWGPrefix remaining v b last := by
  cases point with
  | canonical point=>exact ⟨_,point.residual⟩
  | reserve selected call point=>exact ⟨_,StagingContinuation.reserve_residual selected call point⟩
  | repayment selected guarded call point=>exact ⟨_,StagingContinuation.repayment_residual selected guarded call point⟩
  | queued selected guarded prefixRun restoreRun point=>
    exact ⟨_,StagingContinuation.queued_residual selected guarded prefixRun restoreRun point⟩
  | allocation selected guarded device path=>exact ⟨_,StagingContinuation.allocation_residual selected guarded device path⟩
  | allocationNative selected guarded device point=>
      refine ⟨Allocation.nativeRemainder point >>= CausalJournal.create pid,?_⟩
      rw [(callbackPoint selected guarded).residual]
      change runWGPrefix (state (Journal.allocate _) >>= CausalJournal.create pid) _ _ _=_
      rw [run_bind,run_bind,Allocation.nativeRemainder_run device point]
  | creation selected guarded allocated point=>exact ⟨_,StagingContinuation.create_residual selected guarded allocated point⟩

noncomputable def remainder (point : Point pid w a h v b last) : WGPrefix Event Unit :=
  Classical.choose point.residual

theorem remainder_run (point : Point pid w a h v b last) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a h=runWGPrefix (remainder point) v b last :=
  Classical.choose_spec point.residual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingExpanded
