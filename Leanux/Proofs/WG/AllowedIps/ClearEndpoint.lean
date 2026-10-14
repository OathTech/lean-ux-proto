import Leanux.Proofs.WG.AllowedIps.ClearSnapshot

/-! The two saved-root phases of original WG.free. Normal completion clears
resident lists while node erasures retain surviving values. No traversal totality
or physical retirement of every old node is assumed or asserted. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open ClearSnapshot
set_option maxHeartbeats 1800000
set_option pp.structureInstances false

def freeNodes (ids : List NodeId) : M Unit := do
  for id in ids do freeNode id

def freeRoot (old : Option NodeId) (decision : Decision) : M Unit := do
  if ← branch decision old.isSome then
    if let some root := old then
      rootRemovePeerLists root
      freeNodes (← subtree root)

def resetAllowedips (d : Device) : Device :=
  {d with peerAllowedips := {root4 := none, root6 := none, seq := d.peerAllowedips.seq + 1}}

/-- The saved roots precede the reset and are processed in original family order. -/
theorem free_factor : WG.free = (do
    let d ← getDev
    modifyDev fun current => {current with peerAllowedips := (resetAllowedips d).peerAllowedips}
    freeRoot d.peerAllowedips.root4 .freeHasRoot4
    freeRoot d.peerAllowedips.root6 .freeHasRoot6) := by
  unfold WG.free
  congr 1
  funext d
  cases h4 : d.peerAllowedips.root4 <;> cases h6 : d.peerAllowedips.root6 <;>
    simp [freeRoot, freeNodes, resetAllowedips, branch, h4, h6, bind_assoc]

def SnapshotState (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (k : Kernel) : Prop := ∃ d, k.wg = some d ∧ Progress nodes P [] d

theorem freeNode_snapshot (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (id : NodeId) :
    ⦃fun w => ⌜SnapshotState nodes P w.k⌝⦄ freeNode id
    ⦃⇓? _ w => ⌜SnapshotState nodes P w.k⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w u v hi hr
  obtain ⟨d, hd, hp⟩ := hi
  cases hn : d.nodes[id]? with
  | none => simp [freeNode, getNode, getDev, getK, hd, hn, invariant] at hr
  | some n =>
    obtain ⟨result, finish, he, _, hk⟩ := (total_iff_run _ _ _).mp
      (freeNode_wp w.k d hd id n hn) w rfl
    rw [hr] at he
    cases he
    exact ⟨{d with nodes := d.nodes.erase id}, by rw [hk], hp.erase id⟩

theorem freeNodes_snapshot (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (ids : List NodeId) :
    ⦃fun w => ⌜SnapshotState nodes P w.k⌝⦄ freeNodes ids
    ⦃⇓? _ w => ⌜SnapshotState nodes P w.k⌝⦄ := by
  induction ids with
  | nil => simp only [freeNodes, List.forIn_nil]; mvcgen
  | cons id ids ih =>
    have he : freeNodes (id :: ids) = (do freeNode id; freeNodes ids) := by
      simp [freeNodes, List.forIn_cons, bind_assoc]
    rw [he]
    mvcgen [freeNode_snapshot, ih]

theorem rootRemove_snapshot (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (root : NodeId) (hroot : t.root = some root) (hrep : RepAt nodes width parent t) :
    ⦃fun w => ⌜SnapshotState nodes P w.k⌝⦄ rootRemovePeerLists root
    ⦃⇓? _ w => ⌜SnapshotState nodes (fun pid id => P pid id ∧ id ∉ t.nodeIds) w.k⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w u v hi hr
  cases u
  obtain ⟨d, hd, hp⟩ := hi
  exact ClearSnapshot.root_normal w v nodes P d hd hp root hroot hrep hr

theorem freeRoot_snapshot (nodes : Std.TreeMap Nat AipNode) (P : PeerId → NodeId → Prop)
    (t : Tree) (hrep : RepAt nodes width parent t) (decision : Decision) :
    ⦃fun w => ⌜SnapshotState nodes P w.k⌝⦄ freeRoot t.root decision
    ⦃⇓? _ w => ⌜SnapshotState nodes (fun pid id => P pid id ∧ id ∉ t.nodeIds) w.k⌝⦄ := by
  cases t with
  | empty =>
    mvcgen [freeRoot, Tree.root, branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [SnapshotState, Progress, Tree.nodeIds]
  | node n l r =>
    have hr := rootRemove_snapshot nodes P n.id (t := .node n l r) rfl hrep
    have hs := sameKernel_wp _ (subtree_sameKernel n.id)
      (SnapshotState nodes (fun pid id => P pid id ∧ id ∉ (Tree.node n l r).nodeIds))
    mvcgen [freeRoot, Tree.root, branch, hr, hs, freeNodes_snapshot]

theorem RoutingInvariant.snapshot (hi : RoutingInvariant d t4 t6) :
    Progress d.nodes (fun _ id => id ∈ t4.nodeIds ++ t6.nodeIds) [] d := by
  refine ⟨NodesFrom.refl _, ?_⟩
  intro pid p hp id hid
  obtain ⟨e, he, heid, _⟩ := (hi.lists pid p hp).2 id |>.mp hid
  have hm : id ∈ t4.nodeIds ++ t6.nodeIds := by
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (heid ▸ Tree.entry_mem_nodeIds he)
    · exact List.mem_append_right _ (heid ▸ Tree.entry_mem_nodeIds he)
  exact ⟨hm, by simp, hi.listsOwned pid p hp id hid⟩

/-- A normal whole clear leaves no resident allowed-IP list entries. The node
store need only be a value-preserving submap of the original snapshot. -/
theorem free_snapshot (d : Device) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ WG.free
    ⦃⇓? _ w => ⌜∃ out, w.k.wg = some out ∧ NodesFrom d.nodes out.nodes ∧
      ∀ (pid : PeerId) (p : Peer), out.peers[pid]? = some p → p.allowedipsList = []⌝⦄ := by
  have h4 := freeRoot_snapshot d.nodes (fun _ id => id ∈ t4.nodeIds ++ t6.nodeIds)
    t4 hi.forest.2.2.1 .freeHasRoot4
  have h6 := freeRoot_snapshot d.nodes
    (fun _ id => id ∈ t4.nodeIds ++ t6.nodeIds ∧ id ∉ t4.nodeIds)
    t6 hi.forest.2.2.2 .freeHasRoot6
  rw [← hi.forest.1] at h4
  rw [← hi.forest.2.1] at h6
  have hs : ⦃fun w => ⌜w.k.wg = some d⌝⦄ (do
      modifyDev fun current => {current with peerAllowedips := (resetAllowedips d).peerAllowedips}
      freeRoot d.peerAllowedips.root4 .freeHasRoot4
      freeRoot d.peerAllowedips.root6 .freeHasRoot6)
      ⦃⇓? _ w => ⌜∃ out, w.k.wg = some out ∧ NodesFrom d.nodes out.nodes ∧
        ∀ (pid : PeerId) (p : Peer), out.peers[pid]? = some p → p.allowedipsList = []⌝⦄ := by
    mvcgen [modifyDev, modifyK, h4, h6]
    all_goals try dsimp +zetaDelta only at *
    case vc1 =>
      exact ⟨resetAllowedips d, by simp_all [resetAllowedips], hi.snapshot⟩
    all_goals intros
    all_goals rename_i h
    all_goals obtain ⟨out, hout, hp⟩ := h
    all_goals refine ⟨out, hout, hp.1, ?_⟩
    all_goals intro pid p hpeer
    all_goals apply List.eq_nil_iff_forall_not_mem.mpr
    all_goals intro id hid
    all_goals have hh := hp.2 pid p hpeer id hid
    all_goals rcases List.mem_append.mp hh.1.1.1 with hm | hm
    all_goals first | exact hh.1.1.2 hm | exact hh.1.2 hm
  apply (hoare_iff_triple _ _ _).mp
  intro w u v hd hr
  apply (hoare_iff_triple _ _ _).mpr hs w u v hd
  simpa [free_factor, getDev, getK, hd] using hr

/-- All Kernel/device fields outside the node and peer maps, together with
complete resident peer records with only allowed-IP lists hidden. -/
def clearStoreKernel (k : Kernel) : Kernel × (PeerId → Option Peer) :=
  ({k with wg := k.wg.map (fun d => {d with nodes := {}, peers := {}})},
    fun pid => k.wg.bind (fun d => d.peers[pid]?.map (fun p => {p with allowedipsList := []})))

def clearStoreView (w : World) := clearStoreKernel w.k

theorem rootRemove_storeView (root : NodeId) : SameView clearStoreView (rootRemovePeerLists root) := by
  intro w x v hr
  have he := congrArg (fun kv : Kernel × (PeerId → Option Peer) =>
    ({kv.1 with wg := kv.1.wg.map (fun d : Device => {d with nodes := {}})}, kv.2))
    (rootRemove_clearListView root w x v hr)
  simpa only [clearStoreView, clearStoreKernel, clearListView, Option.map_map, Function.comp_def] using he

theorem freeNode_storeView (id : NodeId) : SameView clearStoreView (freeNode id) := by
  apply SameView.of_wp
  intro s
  mvcgen [freeNode, getNode, getDev, getK, modifyDev, modifyK, invariant]
  all_goals unfold clearStoreView clearStoreKernel at *
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Option.map_map, Option.bind_map, Function.comp_def]

theorem freeNodes_storeView (ids : List NodeId) : SameView clearStoreView (freeNodes ids) := by
  induction ids with
  | nil => exact SameView.pure _ _
  | cons id ids ih =>
    have he : freeNodes (id :: ids) = (do freeNode id; freeNodes ids) := by
      simp [freeNodes, List.forIn_cons, bind_assoc]
    rw [he]
    exact SameView.bind (freeNode_storeView id) (fun _ => ih)

theorem freeRoot_storeView (old : Option NodeId) (decision : Decision) :
    SameView clearStoreView (freeRoot old decision) := by
  apply SameView.of_wp
  intro s
  have hr := fun root => (rootRemove_storeView root).wp (fun t => t = s)
  have hs := fun root => (SameView.of_sameKernel clearStoreKernel (subtree_sameKernel root)).wp (fun t => t = s)
  have hf := fun ids => (freeNodes_storeView ids).wp (fun t => t = s)
  mvcgen [freeRoot, hr, hs, hf, branch]

/-- The reset is the only change visible outside nodes and resident lists. -/
theorem free_storeView (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ WG.free
    ⦃⇓? _ w => ⌜clearStoreView w = clearStoreKernel
      {initial with wg := initial.wg.map resetAllowedips}⌝⦄ := by
  rw [free_factor]
  have hf := fun old dec => (freeRoot_storeView old dec).wp (fun t =>
    t = clearStoreKernel {initial with wg := initial.wg.map resetAllowedips})
  mvcgen [hf, getDev, getK, modifyDev, modifyK, invariant]
  all_goals unfold clearStoreView clearStoreKernel at *
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [resetAllowedips, Option.map_map, Option.bind_map, Function.comp_def]

structure Cleared (d out : Device) : Prop where
  nodes : NodesFrom d.nodes out.nodes
  peers : ∀ pid : PeerId, out.peers[pid]? = d.peers[pid]?.map (fun p => {p with allowedipsList := []})
  frame : out = {d with nodes := out.nodes, peers := out.peers, peerAllowedips := (resetAllowedips d).peerAllowedips}

/-- The whole original normal endpoint has exact peer records and outside
fields; no output invariant is a premise and Stops carry no final World. -/
theorem free_endpoint (w v : World) (d : Device) (hd : w.k.wg = some d)
    (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (hr : WG.free.run w = .ok ((), v)) :
    ∃ out, v.k = {w.k with wg := some out} ∧ Cleared d out := by
  obtain ⟨out, hout, hn, hl⟩ := (hoare_iff_triple _ _ _).mpr (free_snapshot d t4 t6 hi) w () v hd hr
  have hf := (hoare_iff_triple _ _ _).mpr (free_storeView w.k) w () v rfl hr
  have hfirst := congrArg Prod.fst hf
  have hsecond := congrArg Prod.snd hf
  have hk := congrArg (fun k : Kernel => {k with wg := some out}) hfirst
  have hdev := congrArg Kernel.wg hfirst
  have hmask : {out with nodes := {}, peers := {}} =
      {resetAllowedips d with nodes := {}, peers := {}} := by
    simpa [clearStoreView, clearStoreKernel, hd, hout] using hdev
  have hframe := congrArg (fun dev : Device => {dev with nodes := out.nodes, peers := out.peers}) hmask
  change {v.k with wg := some out} = {w.k with wg := some out} at hk
  have hrestore : {v.k with wg := some out} = v.k := by rw [← hout]
  refine ⟨out, hrestore.symm.trans hk, hn, ?_, hframe⟩
  intro pid
  have hp := congrFun hsecond pid
  simp only [clearStoreView, clearStoreKernel, hd, hout, Option.map_some, Option.bind_some] at hp
  cases ho : out.peers[pid]? with
  | none => simpa [ho, resetAllowedips] using hp
  | some p =>
    have he := hl pid p ho
    have heq : {p with allowedipsList := []} = p := by rw [← he]
    rw [ho] at hp
    simp only [Option.map_some, heq] at hp
    exact hp

theorem Cleared.routing (hi : RoutingInvariant d t4 t6) (hc : Cleared d out) :
    RoutingInvariant out .empty .empty := by
  have ht := congrArg Device.peerAllowedips hc.frame
  have hn := congrArg Device.nextNode hc.frame
  have hp := congrArg Device.nextPeer hc.frame
  refine ⟨?_, by trivial, by trivial, by trivial, by trivial, by simp [Tree.nodeIds],
    by simp [Tree.nodeIds], ?_, ?_, ?_, ?_⟩
  · simp [ForestRep, ht, resetAllowedips, Tree.root, RepAt]
  · intro id n hnode
    rw [hn]
    exact hi.below id n (hc.nodes id n hnode)
  · intro pid p hpeer
    rw [hc.peers] at hpeer
    obtain ⟨old, _, rfl⟩ := Option.map_eq_some_iff.mp hpeer
    simp [Tree.entries]
  · simp [OwnersBelow, Tree.entries]
  · intro pid p hpeer
    rw [hc.peers] at hpeer
    obtain ⟨old, hold, _⟩ := Option.map_eq_some_iff.mp hpeer
    rw [hp]
    exact hi.peerSlots pid old hold

end Leanux.Proofs.WG.AllowedIps
