import AllowedipsChildIncoming

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG Root

theorem structureCheck_installedChild_old {s : State} {parentId direction key cidr width pid id : Nat}
    {parentNode node : AipNode} {left right : Option Nat}
    (unique : (s.nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ s.nodes)
    (shape : parentNode.bit=#[left,right]) (bit : direction<2)
    (empty : parentNode.bit[direction]?=some none) (different : id≠s.nextNode) :
    structureCheck (installedChild parentId direction key cidr width pid s) id
        (installChild parentId direction s.nextNode (id,node)).2=structureCheck s id node := by
  have metadata (state : State) : structureCheck state id
      (installChild parentId direction s.nextNode (id,node)).2=structureCheck state id node := by
    by_cases same : id=parentId
    · simp only [installChild,ite_eq_left same]; rfl
    · simp only [installChild,ite_eq_right same]
  rw [metadata,structureCheck_walk,structureCheck_walk]
  have children (before : List Slot) :
      forIn (installedChild parentId direction key cidr width pid s).nodes before (incomingStep id)=
        forIn s.nodes before (incomingStep id) := by
    change forIn ((s.nodes.map (installChild parentId direction s.nextNode))++[_]) before (incomingStep id)=_
    rw [forIn_append_identity (fun pair member current => by
      obtain rfl := List.mem_singleton.mp member
      exact incomingStep_leaf _ _ _ _ _ _ _ _)]
    rw [List.forIn_map]
    apply forIn_congr_mem
    rintro ⟨current,original⟩ present initial
    by_cases same : current=parentId
    · subst current
      have parentEq : original=parentNode := congrArg Prod.snd
        (Option.some.inj ((Trie.find_node_key unique present).symm.trans (Trie.find_node_key unique parent)))
      subst original
      exact incomingStep_child_old shape bit empty different initial
    · simp only [installChild,ite_eq_right same]
  simp only [show (installedChild parentId direction key cidr width pid s).table=s.table from rfl]
  congr 1
  funext incoming
  rw [children]

theorem structureCheck_installedChild_new {s : State} {names memory}
    (parentId direction key cidr width pid : Nat) {parentNode : AipNode} {left right : Option Nat}
    (checked : heap names s memory=.ok ()) (below : ∀ entry ∈ s.nodes, entry.1<s.nextNode)
    (unique : (s.nodes.map Prod.fst).Nodup) (parent : (parentId,parentNode) ∈ s.nodes)
    (shape : parentNode.bit=#[left,right]) (bit : direction<2)
    (empty : parentNode.bit[direction]?=some none) :
    structureCheck (installedChild parentId direction key cidr width pid s) s.nextNode
      {newNode key cidr width (some pid) with parent:=.child parentId direction}=.ok () := by
  have other4 : s.table.root4≠some s.nextNode := by
    intro equal
    have bound : s.nextNode<s.nextNode := roots_below checked below s.nextNode (by simp [equal])
    omega
  have other6 : s.table.root6≠some s.nextNode := by
    intro equal
    have bound : s.nextNode<s.nextNode := roots_below checked below s.nextNode (by simp [equal])
    omega
  have absent : ∀ entry ∈ s.nodes, some s.nextNode ∉ entry.2.bit.toList := by
    rintro ⟨id,node⟩ member child
    have bound : s.nextNode<s.nextNode := edges_below checked below id node member s.nextNode child
    omega
  have children (before : List Slot) :
      forIn (installedChild parentId direction key cidr width pid s).nodes before (incomingStep s.nextNode)=
        .ok (.child parentId direction::before) := by
    change forIn ((s.nodes.map (installChild parentId direction s.nextNode))++[_]) before (incomingStep s.nextNode)=_
    rw [forIn_append_identity (fun pair member current => by
      obtain rfl := List.mem_singleton.mp member
      exact incomingStep_leaf _ _ _ _ _ _ _ _)]
    exact incoming_child_walk unique parent shape bit empty absent before
  rw [structureCheck_walk]
  simp only [installedChild,rootStep,other4,other6,beq_iff_eq,ite_false,List.forIn_cons,List.forIn_nil]
  change (do
    let incoming ← forIn (installedChild parentId direction key cidr width pid s).nodes [] (incomingStep s.nextNode)
    unless incoming==[Slot.child parentId direction] do throw s!"heap.parent[{s.nextNode}]: {repr incoming}")=.ok ()
  rw [children]
  have self : ([Slot.child parentId direction]==[Slot.child parentId direction])=true := by
    change ((parentId==parentId && direction==direction) && true)=true
    simp
  dsimp only [Bind.bind,Except.bind]
  rw [self]
  rfl

#print axioms structureCheck_installedChild_old
#print axioms structureCheck_installedChild_new
end Binary.Pair.Allowedips
