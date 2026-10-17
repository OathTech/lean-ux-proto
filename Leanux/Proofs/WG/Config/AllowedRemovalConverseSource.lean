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
    Ensures (removeNodeSource id n) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.dev = some final ∧ NodeRemoval d id n final) := by
  rw [leaf_source id n shape]
  refine ensures_bind _ _ (leafBeforeParent_effect d id n pairs shape) ?_
  intro u w ambient result final after pre run
  obtain ⟨linked, device, write⟩ := pre
  have lp : NodePairs linked := slotWrite_nodePairs write (nodePairs_write d id _ pairs (by simp [shape]))
  have suffix : Ensures (do let choice ← leafParentDecision n.parent; leafAfterDecision id n choice)
      (fun w => w.dev = some linked)
      (fun result w => result = .yield () ∧ ∃ final, w.dev = some final ∧ NodeRemoval d id n final) := by
    refine ensures_bind _ _ (leafParentDecision_effect linked n.parent) ?_
    intro collapse w ambient result final after pre run
    obtain ⟨device, choice⟩ := pre
    cases collapse with
    | false =>
      obtain ⟨value, ⟨remaining, resident⟩, output⟩ :=
        leafAfterDecision_false_effect linked id n w ambient result final after device run
      exact ⟨value, _, output, .leaf linked shape write choice remaining resident⟩
    | true => exact leafCollapse_node_effect d linked id n lp shape write choice w ambient result final after device run
  exact suffix w ambient result final after device run

/-- Shape chooses the existing structural cases; every other readiness fact
comes from the actual successive reads of a normally returning original body. -/
theorem removeNodeSource_effect_pairs (d : Device) (id : NodeId) (n : AipNode)
    (pairs : NodePairs d) (shape : n.bit.size = 2) :
    Ensures (removeNodeSource id n) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ ∃ final, w.dev = some final ∧ NodeRemoval d id n final) := by
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
      intro w ambient result final after pre run
      obtain ⟨value, output⟩ := removal_returns_ensures_native
        (removeNodeSource_branching d id n left right bits) w ambient result final after pre run
      exact ⟨value, _, output, .branching left right bits⟩

theorem removeEntry_effect_pairs (d : Device) (id : NodeId) (pairs : NodePairs d) :
    Ensures (removeEntry id) (fun w => w.dev = some d)
      (fun result w => result = .yield () ∧ ∃ n next,
        (deleteListedNodes id d d.peers.toList).nodes[id]? = some n ∧
        NodeRemoval (deleteListedNodes id d d.peers.toList) id n next ∧ w.dev = some next) := by
  let unlisted := deleteListedNodes id d d.peers.toList
  have up : NodePairs unlisted := deleteListedNodes_nodePairs id d pairs
  have hg : Ensures (liftAip (getNode id)) (fun g => g.dev = some unlisted)
      (fun n g => g.dev = some unlisted ∧ unlisted.nodes[id]? = some n) := by
    intro g ambient result final after device run
    cases resident : unlisted.nodes[id]? with
    | none =>
      simp [liftAip, getNode, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some n =>
      simp [liftAip, getNode, getDev, modifyDev, device, resident] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl⟩
  unfold removeEntry
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branch .removeListIter true) (fun g : WGWorld => g.dev = some d))) ?_
  intro _
  refine ensures_bind _ _ (removal_returns_ensures_native (listDel_returns id d)) ?_
  intro _
  refine ensures_bind _ _ hg ?_
  intro n g ambient result final after pre run
  obtain ⟨value, output, device, step⟩ :=
    removeNodeSource_effect_pairs unlisted id n up (up id n pre.2)
      g ambient result final after pre.1 run
  exact ⟨value, n, output, pre.2, step, device⟩

theorem removeEntries_effect_pairs (d : Device) (ids : List NodeId) (pairs : NodePairs d) :
    Ensures (removeEntries ids) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ RemovalRun d ids final) := by
  induction ids generalizing d with
  | nil =>
    intro w ambient result final after pre run
    cases run
    exact ⟨d, pre, .nil d⟩
  | cons id rest ih =>
    rw [removeEntries_cons]
    refine ensures_bind _ _ (removeEntry_effect_pairs d id pairs) ?_
    intro result w ambient u final after pre run
    obtain ⟨rfl, n, next, read, step, device⟩ := pre
    obtain ⟨output, actual, tail⟩ := ih next
      (nodeRemoval_nodePairs step (deleteListedNodes_nodePairs id d pairs)) w ambient u final after device run
    exact ⟨output, actual, .cons d id rest n next output read step tail⟩

theorem removeByPeerSource_effect_pairs (d : Device) (p : Peer) (pairs : NodePairs d) :
    Ensures (removeByPeerSource p) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ RemovalEffect d p.allowedipsList final) := by
  have hb (site : Decision) (value : Bool) (P : WGWorld → Prop) :
      Ensures (branch site value : WG.M Bool) P (fun result g => result = value ∧ P g) :=
    (ensures_iff _ _ _).mpr (branch_state_spec P site value)
  rw [removeByPeerSource_entries]
  refine ensures_bind _ _ (hb .removeListEmpty p.allowedipsList.isEmpty (fun g => g.dev = some d)) ?_
  intro empty g ambient result final after pre run
  obtain ⟨rfl, device⟩ := pre
  cases ids : p.allowedipsList with
  | nil =>
    simp only [ids, List.isEmpty_nil, ite_true] at run
    cases run
    exact ⟨d, device, rfl⟩
  | cons id rest =>
    have hm : Ensures (modifyDev bumpAllowedips) (fun g => g.dev = some d)
        (fun _ g => g.dev = some (bumpAllowedips d)) := by
      intro g ambient result final after pre run
      cases run
      simp [pre]
    have tail : Ensures (do
        modifyDev bumpAllowedips
        removeEntries (id :: rest)
        _ ← branch .removeListIter false
        pure () : WG.M Unit)
        (fun g => g.dev = some d)
        (fun _ g => ∃ final, g.dev = some final ∧ RemovalRun (bumpAllowedips d) (id :: rest) final) := by
      refine ensures_bind _ _ hm ?_
      intro _
      refine ensures_bind _ _ (removeEntries_effect_pairs (bumpAllowedips d) (id :: rest) pairs) ?_
      intro _
      refine ensures_bind _ _ (hb .removeListIter false _) ?_
      intro _ g ambient result final after pre run
      cases run
      exact pre.2
    exact tail g ambient result final after device
      (by simpa only [ids, List.isEmpty_cons, Bool.false_eq_true, ite_false] using run)

theorem removeByPeer_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (removeByPeer pid) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ RemovalEffect d p.allowedipsList final) := by
  have hg : Ensures (getPeer pid) (fun g => g.dev = some d)
      (fun result g => result = p ∧ g.dev = some d) := by
    intro g ambient result final after device run
    simp [getPeer, getDev, device, resident] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, device⟩
  rw [removeByPeer_source]
  refine ensures_bind _ _ hg ?_
  intro result g ambient value final after pre run
  obtain ⟨same, device⟩ := pre
  subst result
  exact removeByPeerSource_effect_pairs d p pairs g ambient value final after device run

theorem peerMakeDead_removal_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (peerMakeDead pid) (fun w => w.dev = some d)
      (fun _ _ => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed) := by
  have hu : Ensures (modifyDev (unlistPeer · pid)) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (unlistPeer d pid)) := by
    intro g ambient result final after device run
    cases run
    simp [device]
  rw [peerMakeDead_source]
  refine ensures_bind _ _ hu ?_
  intro u
  refine ensures_bind _ _ (removeByPeer_effect_pairs pid (unlistPeer d pid) p resident pairs) ?_
  intro u w ambient result final after pre run
  obtain ⟨removed, device, steps⟩ := pre
  exact ⟨removed, steps⟩

/-- Recover the witness from the actual successful prefix, then identify the
same original run using the established exact witness-based execution theorem. -/
theorem peerMakeDead_effect_pairs (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Ensures (peerMakeDead pid) (fun w => w.dev = some d)
      (fun _ w => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed ∧
        w.dev = some (deadPeerDevice removed pid p)) := by
  intro w ambient result final after pre run
  obtain ⟨removed, steps⟩ := peerMakeDead_removal_effect_pairs pid d p resident pairs w ambient result final after pre run
  have output := removal_returns_ensures_native (peerMakeDead_returns pid p d removed resident steps)
    w ambient result final after pre run
  exact ⟨removed, steps, output⟩

end Leanux.Proofs.WG.Config
