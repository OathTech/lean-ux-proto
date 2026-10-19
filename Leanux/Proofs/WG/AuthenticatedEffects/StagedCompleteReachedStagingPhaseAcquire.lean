import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseAcquireFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseSelected

/-! Every strict peer-acquire source point retains the selected cohort. Its
last write is justified by the very preceding guard, read and increment;
the original cached peer is not replaced by an unconstrained record. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging.Points
set_option maxHeartbeats 600000
attribute [local implicit_reducible] Native.action peerGet

theorem acquire_covers (owner : PeerId)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (acquireShape owner) w a h := by
  unfold acquireShape
  dsimp only [Covers,id]
  erw [covers_mpr (by simp only [peerGet,lift_bind])]
  have guard:=selected_world (.notPending owner) (native_not_pending owner) before
  apply covers_bind guard
  intro ignored u b middle guarded
  have read:=selected_world (.peer owner) (native_get_peer owner) (guard.normal guarded)
  apply covers_bind read
  intro cached v c last found
  have increment:=selected_world (.inc cached.refcount) (native_inc cached.refcount) (read.normal found)
  apply covers_bind increment
  intro ignored q d events incremented
  refine ⟨increment.normal incremented,?_⟩
  intro returned r e final written
  have whole : runWGPrefix (liftWGPrefix (peerGet owner)) w a h=(.ok ((returned,r),e),final) := by
    rw [peerGet,lift_bind,run_bind]
    erw [guarded]
    dsimp only
    rw [lift_bind,run_bind]
    erw [found]
    dsimp only
    rw [lift_bind,run_bind]
    erw [incremented]
    exact written
  exact preserved (CompleteSelected.acquire_peer (fun _=>id) owner) before whole

theorem allocation_prefix_covers (key : Option KeypairId)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position)
      (allocationPrefixShape pid peer key) w a h := by
  unfold allocationPrefixShape
  have guarded:=guards_covers key before
  apply covers_bind guarded
  intro decision u b middle checked
  cases decision with
  | rejected key invalid=>exact guarded.normal checked
  | unreachable=>exact guarded.normal checked
  | submit kid packets=>
    have owner:=selected_world (.owner kid) (native_owner kid) (guarded.normal checked)
    apply covers_bind owner
    intro pid' v c last read
    have acquired:=acquire_covers pid' (owner.normal read)
    exact covers_bind acquired (fun _ _ _ _ run=>acquired.normal run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
