import Leanux.Proofs.WG.Config.AllowedCollapse

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Pure, locally checked structural alternatives for removing one node's ownership.
All readiness tests use the actual successive maps. This is not a global trie invariant. -/
inductive NodeRemoval (d : Device) (id : NodeId) (n : AipNode) : Device → Prop where
  | branching (left right : NodeId) (shape : n.bit = #[some left, some right]) :
    NodeRemoval d id n (writeNode d id { n with peer := none })
  | unary (child : NodeId) (c : AipNode) (side : Bool)
      (shape : n.bit = if side then #[some child, none] else #[none, some child])
      (childRead : (writeNode d id { n with peer := none }).nodes[child]? = some c)
      (linked : Device) (write : SlotWrite
        (writeNode (writeNode d id { n with peer := none }) child { c with parent := n.parent })
        n.parent (some child) linked)
      (remaining : AipNode) (resident : linked.nodes[id]? = some remaining) :
    NodeRemoval d id n { linked with nodes := linked.nodes.erase id }
  | leaf (linked : Device) (shape : n.bit = #[none, none])
      (write : SlotWrite (writeNode d id { n with peer := none }) n.parent none linked)
      (choice : ParentChoice linked n.parent false)
      (remaining : AipNode) (resident : linked.nodes[id]? = some remaining) :
    NodeRemoval d id n { linked with nodes := linked.nodes.erase id }
  | collapse (detached promoted linked : Device) (parent : NodeId) (bit : Nat)
      (pn leaf pnAfter remaining : AipNode) (sibling : Option NodeId)
      (shape : n.bit = #[none, none]) (location : n.parent = .child parent bit)
      (unlink : SlotWrite (writeNode d id { n with peer := none }) n.parent none detached)
      (choice : ParentChoice detached n.parent true)
      (parentRead : detached.nodes[parent]? = some pn) (siblingRead : pn.bit[1 - bit]? = some sibling)
      (leafRead : detached.nodes[id]? = some leaf)
      (parentAfter : (detached.nodes.erase id)[parent]? = some pnAfter)
      (reparent : ChildReparent { detached with nodes := detached.nodes.erase id } sibling pnAfter.parent promoted)
      (write : SlotWrite promoted pnAfter.parent sibling linked)
      (resident : linked.nodes[parent]? = some remaining) :
    NodeRemoval d id n { linked with nodes := linked.nodes.erase parent }

theorem nodeRemoval_returns {d final : Device} {id : NodeId} {n : AipNode}
    (step : NodeRemoval d id n final) :
    Returns (removeNodeSource id n) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ w.dev = some final) := by
  cases step with
  | branching left right shape => exact removeNodeSource_branching d id n left right shape
  | unary child c side shape childRead linked write remaining resident =>
    exact removeNodeSource_unary d id n child c side shape childRead linked write remaining resident
  | leaf linked shape write choice remaining resident =>
    exact removeNodeSource_leaf_no_collapse d linked id n shape write choice remaining resident
  | collapse detached promoted linked parent bit pn leaf pnAfter remaining sibling shape location unlink choice
      parentRead siblingRead leafRead parentAfter reparent write resident =>
    exact removeNodeSource_leaf_collapse d detached promoted linked id parent bit n pn leaf pnAfter remaining sibling
      shape location unlink choice parentRead siblingRead leafRead parentAfter reparent write resident

/-- Execute removals in the peer-list snapshot order, reading nodes from each evolving state. -/
inductive RemovalRun : Device → List NodeId → Device → Prop where
  | nil (d : Device) : RemovalRun d [] d
  | cons (d : Device) (id : NodeId) (rest : List NodeId) (n : AipNode) (next final : Device)
      (read : (deleteListedNodes id d d.peers.toList).nodes[id]? = some n)
      (step : NodeRemoval (deleteListedNodes id d d.peers.toList) id n next)
      (tail : RemovalRun next rest final) : RemovalRun d (id :: rest) final

def removeEntry (id : NodeId) : WG.M (ForInStep Unit) := do
  _ ← branch .removeListIter true
  listDel id
  let n ← getNode id
  removeNodeSource id n

def removeEntries (ids : List NodeId) : WG.M Unit :=
  forIn ids () (fun id _ => removeEntry id)

theorem removeEntries_cons (id : NodeId) (rest : List NodeId) :
    removeEntries (id :: rest) = (do
      match ← removeEntry id with
      | .done ret => pure ret
      | .yield _ => removeEntries rest) := by
  simp [removeEntries, List.forIn_cons]
  congr 1
  funext result
  cases result <;> rename_i u <;> cases u <;> rfl

theorem removeEntry_returns (d next : Device) (id : NodeId) (n : AipNode)
    (read : (deleteListedNodes id d d.peers.toList).nodes[id]? = some n)
    (step : NodeRemoval (deleteListedNodes id d d.peers.toList) id n next) :
    Returns (removeEntry id) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ w.dev = some next) := by
  have hb : Returns (branch .removeListIter true : WG.M Bool) (fun w => w.dev = some d)
      (fun _ w => w.dev = some d) := by
    intro g ambient device
    exact ⟨true, g, {ambient with steps := ambient.steps.push {
      decision := .removeListIter, outcome := true, netRx := ambient.netRxSection}}, rfl, device⟩
  have hg : Returns (liftAip (getNode id)) (fun w => w.dev = some (deleteListedNodes id d d.peers.toList))
      (fun result w => result = n ∧ w.dev = some (deleteListedNodes id d d.peers.toList)) := by
    intro g ambient device
    refine ⟨n, {g with dev := some (deleteListedNodes id d d.peers.toList)}, ambient, ?_, rfl, rfl⟩
    simp [liftAip, getNode, getDev, modifyDev, device, read]
    rfl
  unfold removeEntry
  refine returns_bind _ _ hb ?_
  intro u
  refine returns_bind _ _ (listDel_returns id d) ?_
  intro u
  refine returns_bind _ _ hg ?_
  intro result w ambient pre
  obtain ⟨value, device⟩ := pre
  subst result
  exact nodeRemoval_returns step w ambient device

theorem removalRun_returns {d final : Device} {ids : List NodeId} (steps : RemovalRun d ids final) :
    Returns (removeEntries ids) (fun w => w.dev = some d)
      (fun _ w => w.dev = some final) := by
  induction steps with
  | nil d =>
    intro w ambient device
    exact ⟨(), w, ambient, rfl, device⟩
  | cons d id rest n next final read step tail ih =>
    rw [removeEntries_cons]
    refine returns_bind _ _ (removeEntry_returns d next id n read step) ?_
    intro result w ambient pre
    obtain ⟨value, device⟩ := pre
    subst result
    exact ih w ambient device

def RemovalEffect (d : Device) (ids : List NodeId) (final : Device) : Prop :=
  match ids with
  | [] => final = d
  | _ :: _ => RemovalRun (bumpAllowedips d) ids final

theorem removeByPeerSource_entries (p : Peer) :
    removeByPeerSource p = (do
      if ← branch .removeListEmpty p.allowedipsList.isEmpty then return
      modifyDev bumpAllowedips
      removeEntries p.allowedipsList
      _ ← branch .removeListIter false
      pure ()) := rfl

theorem removeByPeerSource_general (p : Peer) (d final : Device)
    (steps : RemovalEffect d p.allowedipsList final) :
    Returns (removeByPeerSource p) (fun w => w.dev = some d)
      (fun _ w => w.dev = some final) := by
  have hb (site : Decision) (value : Bool) (entry : Device) :
      Returns (branch site value : WG.M Bool) (fun g => g.dev = some entry)
        (fun result g => result = value ∧ g.dev = some entry) := by
    intro g ambient device
    exact ⟨value, g, {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}}, rfl, rfl, device⟩
  rw [removeByPeerSource_entries]
  refine returns_bind _ _ (hb .removeListEmpty p.allowedipsList.isEmpty d) ?_
  intro empty g ambient pre
  obtain ⟨rfl, device⟩ := pre
  cases ids : p.allowedipsList with
  | nil =>
    have same : final = d := by simpa [RemovalEffect, ids] using steps
    subst final
    simp only [List.isEmpty_nil, ite_true]
    exact ⟨(), g, ambient, rfl, device⟩
  | cons id rest =>
    have chain : RemovalRun (bumpAllowedips d) (id :: rest) final := by
      simpa [RemovalEffect, ids] using steps
    have hm : Returns (modifyDev bumpAllowedips) (fun g => g.dev = some d)
        (fun _ g => g.dev = some (bumpAllowedips d)) := by
      intro g ambient device
      refine ⟨(), {g with dev := some (bumpAllowedips d)}, ambient, ?_, rfl⟩
      simp [modifyDev, device]
      rfl
    have tail : Returns (do
        modifyDev bumpAllowedips
        removeEntries (id :: rest)
        _ ← branch .removeListIter false
        pure ()) (fun g => g.dev = some d) (fun _ g => g.dev = some final) := by
      refine returns_bind _ _ hm ?_
      intro _
      refine returns_bind _ _ (removalRun_returns chain) ?_
      intro _
      refine returns_bind _ _ (hb .removeListIter false final) ?_
      intro result g ambient pre
      exact ⟨(), g, ambient, rfl, pre.2⟩
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
    exact tail g ambient device

theorem removeByPeer_general (pid : PeerId) (p : Peer) (d final : Device)
    (resident : d.peers[pid]? = some p) (steps : RemovalEffect d p.allowedipsList final) :
    Returns (removeByPeer pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some final) := by
  have hg : Returns (getPeer pid) (fun w => w.dev = some d)
      (fun result w => result = p ∧ w.dev = some d) := by
    intro g ambient device
    refine ⟨p, g, ambient, ?_, rfl, device⟩
    simp [getPeer, getDev, device, resident]
    rfl
  rw [removeByPeer_source]
  refine returns_bind _ _ hg ?_
  intro result w ambient pre
  obtain ⟨value, device⟩ := pre
  subst result
  exact removeByPeerSource_general p d final steps w ambient device

end Leanux.Proofs.WG.Config
