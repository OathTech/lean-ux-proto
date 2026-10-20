import AllowedipsTrieEdgeWalk

namespace Binary.Pair.Trie
open Leanux Leanux.WG

def nodeChildren (entry : NodeId×Node) : List NodeId :=
  entry.2.children.toList.zipIdx.flatMap edgeChildren

theorem nodeStep_of_facts {s roots entry before}
    (valid : ∀ edge ∈ entry.2.children.toList.zipIdx, EdgeFacts s roots entry.2 edge)
    (distinct : (nodeChildren entry++before).Nodup) :
    nodeStep s roots entry before=.ok (.yield ((nodeChildren entry).reverse++before)) := by
  unfold nodeStep
  rw [edgeWalk_of_facts valid distinct]
  rfl

theorem nodeStep_resources {s roots entry before after} (initial : before.Nodup)
    (run : nodeStep s roots entry before=.ok after) :
    (nodeChildren entry++before).Nodup ∧ after=.yield ((nodeChildren entry).reverse++before) := by
  unfold nodeStep at run
  obtain ⟨next,walk,run⟩ := bind_ok run
  have distinct := edgeWalk_nodup initial walk
  have valid := forIn_ok (P:=EdgeFacts s roots entry.2)
    (fun _ _ _ _ step => by
      obtain ⟨⟨next,equal⟩,facts⟩ := edgeStep_facts step
      exact ⟨next,equal,facts⟩) walk
  have equal := Except.ok.inj (walk.symm.trans (edgeWalk_of_facts valid distinct))
  exact ⟨distinct,(Except.ok.inj run).symm.trans (congrArg ForInStep.yield equal)⟩

private theorem collect_permutation (first rest before : List NodeId) :
    (first++rest++before).Perm (rest++first.reverse++before) :=
  List.Perm.append_right before (List.perm_append_comm.trans
    (List.Perm.append_left rest (List.reverse_perm first).symm))

theorem nodeWalk_of_facts {s roots} {nodes : List (NodeId×Node)} {before : List NodeId}
    (valid : ∀ entry ∈ nodes, ∀ edge ∈ entry.2.children.toList.zipIdx, EdgeFacts s roots entry.2 edge)
    (distinct : (nodes.flatMap nodeChildren++before).Nodup) :
    forIn nodes before (nodeStep s roots)=.ok ((nodes.flatMap nodeChildren).reverse++before) := by
  induction nodes generalizing before with
  | nil => rfl
  | cons entry nodes ih =>
    have expanded : (nodeChildren entry++(nodes.flatMap nodeChildren++before)).Nodup := by
      simpa only [List.flatMap_cons,List.append_assoc] using distinct
    have headDistinct : (nodeChildren entry++before).Nodup :=
      List.Nodup.sublist ((List.sublist_append_right (nodes.flatMap nodeChildren) before).append_left _) expanded
    have nextDistinct : (nodes.flatMap nodeChildren++((nodeChildren entry).reverse++before)).Nodup := by
      simpa only [List.append_assoc] using (collect_permutation (nodeChildren entry) (nodes.flatMap nodeChildren) before).nodup
        (by simpa only [List.append_assoc] using expanded)
    rw [List.forIn_cons,nodeStep_of_facts (valid entry (by simp)) headDistinct]
    dsimp only [Bind.bind,Except.bind]
    have result := ih (fun e member => valid e (List.mem_cons_of_mem entry member)) nextDistinct
    simpa only [List.flatMap_cons,List.reverse_append,List.append_assoc] using result

theorem nodeWalk_nodup {s roots} {nodes : List (NodeId×Node)} {before after : List NodeId}
    (initial : before.Nodup) (run : forIn nodes before (nodeStep s roots)=.ok after) :
    (nodes.flatMap nodeChildren++before).Nodup := by
  induction nodes generalizing before with
  | nil => exact initial
  | cons entry nodes ih =>
    rw [List.forIn_cons] at run
    obtain ⟨step,first,run⟩ := bind_ok run
    obtain ⟨headDistinct,rfl⟩ := nodeStep_resources initial first
    have nextInitial : ((nodeChildren entry).reverse++before).Nodup :=
      (List.Perm.append_right before (List.reverse_perm (nodeChildren entry)).symm).nodup headDistinct
    have later := ih nextInitial run
    have moved := (collect_permutation (nodeChildren entry) (nodes.flatMap nodeChildren) before).symm.nodup
      (by simpa only [List.append_assoc] using later)
    simpa only [List.flatMap_cons] using moved

theorem heap_children_nodup {s : State} {roots : List (Option NodeId)} (checked : heap s roots=.ok ()) :
    (s.nodes.flatMap nodeChildren).Nodup := by
  rw [heap_walk] at checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,walk,_⟩ := bind_ok checked
  simpa only [List.append_nil] using nodeWalk_nodup (by simp) walk

/-- Re-establish the unchanged executable heap check from explicit graph facts.
The facts are about the modeled node graph, not a binary execution certificate. -/
theorem heap_of_facts {s : State} {roots : List (Option NodeId)}
    (present : ∀ id, some id ∈ roots → ∃ node, (id,node) ∈ s.nodes)
    (valid : ∀ id node, (id,node) ∈ s.nodes → ∀ edge ∈ node.children.toList.zipIdx, EdgeFacts s roots node edge)
    (distinct : (s.nodes.flatMap nodeChildren).Nodup) : heap s roots=.ok () := by
  have rootChecks : checkEach roots (rootCheck s.nodes)=.ok () := by
    apply (checkEach_ok _ _).mpr
    intro root member
    cases root with
    | none => rfl
    | some id =>
      obtain ⟨node,atNode⟩ := present id member
      apply check_of
      · exact List.any_eq_true.mpr ⟨(id,node),atNode,by simp⟩
      · rfl
  rw [heap_walk,rootChecks]
  dsimp only [Bind.bind,Except.bind]
  rw [nodeWalk_of_facts (fun entry member => valid entry.1 entry.2 member)
    (by simpa only [List.append_nil] using distinct)]
  rfl

#print axioms heap_children_nodup
#print axioms heap_of_facts
end Binary.Pair.Trie
