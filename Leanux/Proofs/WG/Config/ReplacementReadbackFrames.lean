import Leanux.Proofs.WG.Config.ReplacementReadbackModel
import Leanux.Proofs.WG.Config.AllowedRemovalFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean

/-- Reference acquisition commutes with pure allowed-IP list removal. -/
theorem erasePeerList_refcount_update (ids : List NodeId) (p : Peer) (count : Nat) :
    erasePeerList ids {p with refcount := count} =
      {erasePeerList ids p with refcount := count} := by
  induction ids generalizing p with
  | nil => rfl
  | cons id rest ih =>
    simp only [erasePeerList,eraseListedPeer]
    exact ih {p with allowedipsList := listRemove p.allowedipsList id}

/-- Structural removal preserves all fields outside its stores/table. -/
theorem removalRun_readback_outer {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : replacementOuter final = replacementOuter d := by
  induction steps with
  | nil => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih]
    have hs := congrArg replacementOuter (nodeRemoval_frame step)
    have hd := congrArg replacementOuter (deleteListedNodes_withoutPeers id d d.peers.toList)
    exact hs.trans hd

/-- The nonempty removal sequence's table increment does not change outer fields. -/
theorem removalEffect_readback_outer {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) : replacementOuter final = replacementOuter d := by
  cases ids with
  | nil => subst final; rfl
  | cons id rest =>
    have h := removalRun_readback_outer steps
    exact h

end Leanux.Proofs.WG.Config
