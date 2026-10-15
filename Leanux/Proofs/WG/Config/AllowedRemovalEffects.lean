import Leanux.Proofs.WG.Config.AllowedRemoval

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Fields outside the node store and the two allowed-IP roots; sequence is retained. -/
def withoutTrie (d : Device) : Device :=
  { d with nodes := {}, peerAllowedips := { d.peerAllowedips with root4 := none, root6 := none } }

theorem slotWrite_frame {d final : Device} {slot : Slot} {value : Option NodeId}
    (write : SlotWrite d slot value final) : withoutTrie final = withoutTrie d := by
  cases write <;> rfl

theorem childReparent_frame {d final : Device} {child : Option NodeId} {slot : Slot}
    (write : ChildReparent d child slot final) : withoutTrie final = withoutTrie d := by
  cases write <;> rfl

theorem nodeRemoval_frame {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) : withoutTrie final = withoutTrie d := by
  cases step with
  | branching left right shape => rfl
  | unary child c side shape childRead linked write remaining resident =>
    simpa only [withoutTrie, writeNode] using slotWrite_frame write
  | leaf linked shape write choice remaining resident => simpa only [withoutTrie, writeNode] using slotWrite_frame write
  | collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling shape location unlink choice
      parentRead siblingRead leafRead parentAfter reparent write resident =>
    have h1 := slotWrite_frame write
    have h2 := childReparent_frame reparent
    have h3 := slotWrite_frame unlink
    simpa only [withoutTrie, writeNode] using h1.trans (h2.trans h3)

theorem nodeRemoval_peers {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) : final.peers = d.peers := by
  simpa only [withoutTrie] using congrArg Device.peers (nodeRemoval_frame step)

def erasePeerList : List NodeId → Peer → Peer
  | [], p => p
  | id :: rest, p => erasePeerList rest (eraseListedPeer id p)

theorem removalRun_peers {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) (pid : PeerId) :
    final.peers[pid]? = d.peers[pid]?.map (erasePeerList ids) := by
  induction steps with
  | nil d => simp [erasePeerList]
  | cons d id rest n next final read step tail ih =>
    rw [ih, nodeRemoval_peers step, deleteListedNodes_lookup]
    simp [Option.map_map, Function.comp_def, erasePeerList]

theorem erasePeerList_refcount (ids : List NodeId) (p : Peer) :
    (erasePeerList ids p).refcount = p.refcount := by
  induction ids generalizing p with
  | nil => rfl
  | cons id rest ih => exact ih (eraseListedPeer id p)

theorem erasePeerList_identity (ids : List NodeId) (p : Peer) :
    (erasePeerList ids p).internalId = p.internalId := by
  induction ids generalizing p with
  | nil => rfl
  | cons id rest ih => exact ih (eraseListedPeer id p)

theorem removalRun_running {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : final.running = d.running := by
  induction steps with
  | nil d => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih]
    have h1 := congrArg Device.running (nodeRemoval_frame step)
    have h2 := congrArg Device.running (deleteListedNodes_withoutPeers id d d.peers.toList)
    simpa only [withoutTrie, withoutPeers] using h1.trans h2

theorem removalEffect_peers {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) (pid : PeerId) :
    final.peers[pid]? = d.peers[pid]?.map (erasePeerList ids) := by
  cases ids with
  | nil => subst final; simp [erasePeerList]
  | cons id rest => exact removalRun_peers steps pid

theorem removalEffect_running {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) : final.running = d.running := by
  cases ids with
  | nil => subst final; rfl
  | cons id rest =>
    have h := removalRun_running steps
    exact h

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

theorem nodeRemoval_seq {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) : final.peerAllowedips.seq = d.peerAllowedips.seq := by
  simpa only [withoutTrie] using congrArg (fun d => d.peerAllowedips.seq) (nodeRemoval_frame step)

theorem removalRun_seq {d final : Device} {ids : List NodeId}
    (steps : RemovalRun d ids final) : final.peerAllowedips.seq = d.peerAllowedips.seq := by
  induction steps with
  | nil d => rfl
  | cons d id rest n next final read step tail ih =>
    rw [ih, nodeRemoval_seq step, deleteListedNodes_allowedips]

theorem removalEffect_seq {d final : Device} {ids : List NodeId}
    (steps : RemovalEffect d ids final) :
    final.peerAllowedips.seq = d.peerAllowedips.seq + (if ids.isEmpty then 0 else 1) := by
  cases ids with
  | nil => subst final; simp
  | cons id rest =>
    have h := removalRun_seq steps
    simpa [bumpAllowedips] using h

end Leanux.Proofs.WG.Config
