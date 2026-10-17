import Leanux.Proofs.WG.Config.AllowedRemovalConverseBranches
import Leanux.Proofs.WG.Config.AllowedRemovalConverseLeaves
import Leanux.Proofs.WG.Config.AllowedPairsEffects
import Leanux.Proofs.WG.Config.PeerDead

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem removeNodeSource_leaf_effect (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit = #[none, none]) :
    Ensures (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
  rw [leaf_source id n shape]
  refine ensures_bind _ _ (leafBeforeParent_effect d id n pairs shape) ?_
  intro u w result final pre run
  obtain ⟨linked, device, write⟩ := pre
  have lp : NodePairs linked := slotWrite_nodePairs write (nodePairs_write d id _ pairs (by simp [shape]))
  have suffix : Ensures (do let choice ← leafParentDecision n.parent; leafAfterDecision id n choice)
      (fun w => w.k.wg = some linked)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
    refine ensures_bind _ _ (leafParentDecision_effect linked n.parent) ?_
    intro collapse w result final pre run
    obtain ⟨device, choice⟩ := pre
    cases collapse with
    | false =>
      obtain ⟨value, ⟨remaining, resident⟩, output⟩ :=
        leafAfterDecision_false_effect linked id n w result final device run
      exact ⟨value, _, output, .leaf linked shape write choice remaining resident⟩
    | true => exact leafCollapse_node_effect d linked id n lp shape write choice w result final device run
  exact suffix w result final device run

/-- Shape chooses the existing structural cases; every other readiness fact
comes from the actual successive reads of a normally returning original body. -/
theorem removeNodeSource_effect_pairs (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit.size = 2) :
    Ensures (removeNodeSource id n) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.k.wg = some final ∧ NodeRemoval d id n final) := by
  obtain ⟨left, right, bits⟩ := array_pair_shape n.bit shape
  cases left with
  | none =>
    cases right with
    | none => exact removeNodeSource_leaf_effect d id n pairs bits
    | some child => exact removeNodeSource_unary_effect d id n child false pairs bits
  | some left =>
    cases right with
    | none => exact removeNodeSource_unary_effect d id n left true pairs bits
    | some right =>
      intro w result final pre run
      obtain ⟨value, output⟩ := removal_returns_ensures
        (removeNodeSource_branching d id n left right bits) w result final pre run
      exact ⟨value, _, output, .branching left right bits⟩

theorem removeEntry_effect_pairs (d : Device) (id : NodeId) (pairs : NodePairs d) :
    Ensures (removeEntry id) (fun w => w.k.wg = some d)
      (fun result w => result = .yield () ∧ ∃ n next,
        (deleteListedNodes id d d.peers.toList).nodes[id]? = some n ∧
        NodeRemoval (deleteListedNodes id d d.peers.toList) id n next ∧ w.k.wg = some next) := by
  let unlisted := deleteListedNodes id d d.peers.toList
  have up : NodePairs unlisted := deleteListedNodes_nodePairs id d pairs
  have hl := (returns_iff _ _ _).mp (listDel_returns id d)
  have hn := fun n shape => (ensures_iff _ _ _).mp (removeNodeSource_effect_pairs unlisted id n up shape)
  rw [ensures_iff]
  mvcgen [removeEntry, branch, getNode, getDev, getK, invariant, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals rename_i n hdevice resident
  all_goals have shape := up id n resident
  all_goals have spec := hn n shape
  all_goals mvcgen [spec]
  all_goals try dsimp +zetaDelta only at *
  all_goals grind

theorem removeEntries_effect_pairs (d : Device) (ids : List NodeId) (pairs : NodePairs d) :
    Ensures (removeEntries ids) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RemovalRun d ids final) := by
  induction ids generalizing d with
  | nil =>
    intro w result final pre run
    change Except.ok ((), w) = .ok (result, final) at run
    cases run
    exact ⟨d, pre, .nil d⟩
  | cons id rest ih =>
    rw [removeEntries_cons]
    refine ensures_bind _ _ (removeEntry_effect_pairs d id pairs) ?_
    intro result w u final pre run
    obtain ⟨rfl, n, next, read, step, device⟩ := pre
    obtain ⟨output, actual, tail⟩ := ih next
      (nodeRemoval_nodePairs step (deleteListedNodes_nodePairs id d pairs)) w u final device run
    exact ⟨output, actual, .cons d id rest n next output read step tail⟩

theorem removeByPeerSource_effect_pairs (d : Device) (p : Peer) (pairs : NodePairs d) :
    Ensures (removeByPeerSource p) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RemovalEffect d p.allowedipsList final) := by
  rw [removeByPeerSource_entries]
  cases ids : p.allowedipsList with
  | nil =>
    rw [ensures_iff]
    simp only [ids]
    mvcgen [branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [RemovalEffect]
  | cons id rest =>
    have hr := (ensures_iff _ _ _).mp (removeEntries_effect_pairs (bumpAllowedips d) (id :: rest) pairs)
    rw [ensures_iff]
    simp only [ids]
    mvcgen [branch, modifyDev, modifyK, hr]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [RemovalEffect, bumpAllowedips]

theorem removeByPeer_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (removeByPeer pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RemovalEffect d p.allowedipsList final) := by
  have hr := (ensures_iff _ _ _).mp (removeByPeerSource_effect_pairs d p pairs)
  rw [removeByPeer_source, ensures_iff]
  mvcgen [getPeer, getDev, getK, invariant, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals subst_vars
  all_goals mvcgen [hr]

theorem peerMakeDead_removal_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (peerMakeDead pid) (fun w => w.k.wg = some d)
      (fun _ _ => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed) := by
  have hu : Ensures (modifyDev (unlistPeer · pid)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (unlistPeer d pid)) := by
    rw [ensures_iff]
    mvcgen [modifyDev, modifyK]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  rw [peerMakeDead_source]
  refine ensures_bind _ _ hu ?_
  intro u
  refine ensures_bind _ _ (removeByPeer_effect_pairs pid (unlistPeer d pid) p resident pairs) ?_
  intro u w result final pre run
  obtain ⟨removed, device, steps⟩ := pre
  exact ⟨removed, steps⟩

/-- Recover the witness from the actual successful prefix, then identify the
same original run using the established exact witness-based execution theorem. -/
theorem peerMakeDead_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (peerMakeDead pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed ∧
        w.k.wg = some (deadPeerDevice removed pid p)) := by
  intro w result final pre run
  obtain ⟨removed, steps⟩ := peerMakeDead_removal_effect_pairs pid d p resident pairs w result final pre run
  have output := removal_returns_ensures (peerMakeDead_returns pid p d removed resident steps)
    w result final pre run
  exact ⟨removed, steps, output⟩

end Leanux.Proofs.WG.Config
