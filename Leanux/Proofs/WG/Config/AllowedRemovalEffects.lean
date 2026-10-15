import Leanux.Proofs.WG.Config.AllowedRemovalFrames
import Leanux.Proofs.WG.Config.AllowedRemoval

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem removalRun_peers {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) (pid : PeerId) :
    final.peers[pid]? = d.peers[pid]?.map (erasePeerList ids) := by
  induction steps with
  | nil d => simp [erasePeerList]
  | cons d id rest n next final read step tail ih =>
    rw [ih, nodeRemoval_peers step, deleteListedNodes_lookup]
    simp [Option.map_map, Function.comp_def, erasePeerList]

theorem removalEffect_peers {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) (pid : PeerId) :
    final.peers[pid]? = d.peers[pid]?.map (erasePeerList ids) := by
  cases ids with
  | nil => subst final; simp [erasePeerList]
  | cons id rest => exact removalRun_peers steps pid

theorem erasePeerList_allowedips (ids : List NodeId) (p : Peer) :
    (erasePeerList ids p).allowedipsList = p.allowedipsList.filter (fun id => !ids.contains id) := by
  induction ids generalizing p with
  | nil =>
    simp only [erasePeerList, List.contains_nil, Bool.not_false]
    exact (List.filter_eq_self.mpr (by intro a member; rfl)).symm
  | cons id rest ih =>
    simp [erasePeerList, ih, eraseListedPeer, listRemove, List.filter_filter,
      Bool.not_or, Bool.and_comm, bne_eq]
    apply List.filter_congr
    intro a member
    by_cases same : a = id <;> simp [same]

theorem erasePeerList_own_empty (p : Peer) :
    (erasePeerList p.allowedipsList p).allowedipsList = [] := by
  rw [erasePeerList_allowedips]
  simp only [List.filter_eq_nil_iff]
  intro id member
  simpa using member

theorem removalEffect_seq {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) :
    final.peerAllowedips.seq = d.peerAllowedips.seq + (if ids.isEmpty then 0 else 1) := by
  cases ids with
  | nil => subst final; simp
  | cons id rest =>
    have h := removalRun_seq steps
    simpa [bumpAllowedips] using h

end Leanux.Proofs.WG.Config
