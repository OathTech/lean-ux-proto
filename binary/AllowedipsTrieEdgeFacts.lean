import AllowedipsTrieLeaf

namespace Binary.Pair.Trie
open Leanux Leanux.WG

/-- Mathematical facts read by the existing executable edge assertion. These
are derived from it, and do not replace its repeated-parent/root checks. -/
def EdgeFacts (s : State) (roots : List (Option NodeId)) (node : Node)
    (edge : Option NodeId×Nat) : Prop :=
  ∀ next, edge.1=some next → ∃ child,
    s.nodes.find? (·.1==next)=some (next,child) ∧ some next ∉ roots ∧
    child.width=node.width ∧ node.cidr<child.cidr ∧
    child.key/2^(node.width-node.cidr)=node.key/2^(node.width-node.cidr) ∧
    child.key/2^(node.width-1-node.cidr)%2=edge.2

theorem edgeStep_facts {s roots id node edge before after}
    (run : edgeStep s roots id node edge before=.ok after) :
    (∃ next, after=.yield next) ∧ EdgeFacts s roots node edge := by
  rcases edge with ⟨child,bit⟩
  cases child with
  | none => exact ⟨⟨before,(Except.ok.inj run).symm⟩,by intro next equal; cases equal⟩
  | some next =>
    unfold edgeStep at run
    cases found : s.nodes.find? (·.1==next) with
    | none => simp only [found] at run; cases run
    | some pair =>
      rcases pair with ⟨current,child⟩
      simp only [found] at run
      split at run
      · cases run
      · split at run
        · cases run
        · rename_i notRoot
          obtain ⟨measure,run⟩ := check_ok _ _ _ _ run
          obtain ⟨prefixEq,run⟩ := check_ok _ _ _ _ run
          obtain ⟨side,run⟩ := check_ok _ _ _ _ run
          have identity : current=next := by simpa using List.find?_some found
          subst current
          have measure : child.width=node.width ∧ node.cidr<child.cidr := by simpa using measure
          refine ⟨⟨next::before,(Except.ok.inj run).symm⟩,?_⟩
          intro actual equal
          cases Option.some.inj equal
          exact ⟨child,found,by simpa using notRoot,measure.1,measure.2,eq_of_beq prefixEq,eq_of_beq side⟩

theorem heap_edge_facts {s : State} {roots : List (Option NodeId)}
    (checked : heap s roots=.ok ()) :
    ∀ id node, (id,node) ∈ s.nodes → ∀ edge ∈ node.children.toList.zipIdx,
      EdgeFacts s roots node edge := by
  rw [heap_walk] at checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,walk,_⟩ := bind_ok checked
  have all := forIn_ok (P:=fun entry : NodeId×Node =>
      ∀ edge ∈ entry.2.children.toList.zipIdx, EdgeFacts s roots entry.2 edge)
    (fun entry _ before after run => by
      unfold nodeStep at run
      obtain ⟨next,inner,run⟩ := bind_ok run
      exact ⟨next,(Except.ok.inj run).symm,forIn_ok (P:=EdgeFacts s roots entry.2)
        (fun _ _ _ _ step => by
          obtain ⟨⟨next,eq⟩,facts⟩ := edgeStep_facts step
          exact ⟨next,eq,facts⟩) inner⟩) walk
  intro id node member
  exact all (id,node) member

def edgeChildren (edge : Option NodeId×Nat) : List NodeId := edge.1.toList

theorem edgeStep_of_facts {s roots id node edge before}
    (facts : EdgeFacts s roots node edge)
    (fresh : ∀ next ∈ edgeChildren edge, next ∉ before) :
    edgeStep s roots id node edge before=.ok (.yield (edgeChildren edge++before)) := by
  rcases edge with ⟨child,bit⟩
  cases child with
  | none => rfl
  | some next =>
    obtain ⟨child,found,notRoot,width,measure,prefixEq,side⟩ := facts next rfl
    have absent := fresh next (by simp [edgeChildren])
    simp only [edgeStep,found,show before.contains next=false from by simpa using absent,
      show roots.contains (some next)=false from by simpa using notRoot,Bool.false_eq_true,
      ite_false,width,beq_self_eq_true,measure,decide_true,Bool.true_and,ite_true,prefixEq,side]
    rfl

#print axioms heap_edge_facts
end Binary.Pair.Trie
