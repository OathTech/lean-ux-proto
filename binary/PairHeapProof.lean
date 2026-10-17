import PairTrieFields
import PairAllowedips

namespace Binary.Pair.Trie
open Leanux Leanux.WG

theorem Reconstructed.node {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {d : Device} (fields : Reconstructed names o m (target d))
    {id : Nat} {node : AipNode} (present : d.nodes.get? id = some node) :
    ∃ a, (id,a) ∈ names.nodes ∧ decodeNode names o m a = .ok (targetNode node) := by
  have member : (id,targetNode node) ∈ (target d).nodes := by
    apply List.mem_map.mpr
    exact ⟨(id,node),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,rfl⟩
  obtain ⟨⟨id',a⟩,named,eq,decoded⟩ := fields.nodes.right _ member
  subst id'
  exact ⟨a,named,decoded⟩

theorem target_node {d : Device} {id : Nat} {node : Node}
    (member : (id,node) ∈ (target d).nodes) :
    ∃ source, d.nodes.get? id = some source ∧ targetNode source = node := by
  obtain ⟨⟨id',source⟩,present,equal⟩ := List.mem_map.mp member
  obtain ⟨identity,equalNode⟩ : id' = id ∧ targetNode source = node := Prod.mk.inj equal
  subst id'
  exact ⟨source,Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp present,equalNode⟩

theorem heap_edges {s : State} {roots : List (Option Nat)} (ok : heap s roots = .ok ()) :
    ∀ id node, (id,node) ∈ s.nodes → ∀ next, some next ∈ node.children.toList →
      ∃ child, (next,child) ∈ s.nodes ∧ child.width = node.width := by
  unfold heap at ok
  obtain ⟨rootChecks,rootsOk,ok⟩ := bind_ok ok
  obtain ⟨parents,parentsOk,ok⟩ := bind_ok ok
  have outer := forIn_ok (P := fun pair : Nat×Node =>
      ∀ next, some next ∈ pair.2.children.toList →
        ∃ child, (next,child) ∈ s.nodes ∧ child.width = pair.2.width) (fun pair _ before after run => by
    obtain ⟨parents,childrenOk,run⟩ := bind_ok run
    refine ⟨parents,(Except.ok.inj run).symm,?_⟩
    have inner := forIn_ok (P := fun pair' : Option Nat×Nat =>
        ∀ next, pair'.1 = some next → ∃ child, (next,child) ∈ s.nodes ∧ child.width = pair.2.width)
      (fun entry _ before after run => by
        rcases entry with ⟨child,bit⟩
        cases child with
        | none => exact ⟨before,(Except.ok.inj run).symm,by intros; contradiction⟩
        | some next =>
          simp only [] at run
          cases found : s.nodes.find? (·.1 == next) with
          | none => simp only [found] at run; cases run
          | some child =>
            simp only [found] at run
            split at run
            · cases run
            · split at run
              · cases run
              · obtain ⟨measure,run⟩ := check_ok _ _ _ _ run
                obtain ⟨prefixCheck,run⟩ := check_ok _ _ _ _ run
                obtain ⟨side,run⟩ := check_ok _ _ _ _ run
                refine ⟨next::before,(Except.ok.inj run).symm,?_⟩
                intro id equal
                cases Option.some.inj equal
                have identity : child.1 = next := by simpa using List.find?_some found
                have family : child.2.width = pair.2.width ∧ pair.2.cidr < child.2.cidr := by simpa using measure
                exact ⟨child.2,identity ▸ List.mem_of_find?_eq_some found,family.1⟩) childrenOk
    intro next member
    obtain ⟨i,atIndex⟩ := List.mem_iff_getElem?.mp member
    exact inner (some next,i) (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex) next rfl) parentsOk
  intro id node member
  exact outer (id,node) member

theorem assertAt_ok {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {w : World} (ok : assertAt names o m w = .ok ()) :
    ∃ d, w.k.wg = some d ∧ Corresponds names o m d ∧
      heap (target d) [d.peerAllowedips.root4,d.peerAllowedips.root6] = .ok () := by
  unfold assertAt at ok
  cases device : w.k.wg with
  | none => rw [device] at ok; cases ok
  | some d =>
    rw [device] at ok
    obtain ⟨actual,decoded,ok⟩ := bind_ok ok
    obtain ⟨nodes,ok⟩ := check_ok _ _ _ _ ok
    obtain ⟨counts,ok⟩ := check_ok _ _ _ _ ok
    have equal : actual = target d := by
      cases actual
      have ns := eq_of_beq nodes
      have ps := eq_of_beq counts
      cases ns
      cases ps
      rfl
    subst actual
    exact ⟨d,rfl,mapError_ok decoded,ok⟩

theorem callInput_ok {names : Names} {o : AllowedipsProbe.Offsets} {m : DataMem}
    {d : Device} {root : Option NodeId} {bits query : Nat}
    (related : Corresponds names o m d) (ok : callInput names o m root bits query = .ok ()) :
    (bits = 32 ∨ bits = 128) ∧ query < 2^bits ∧
      ∀ id, root = some id → ∃ node, d.nodes.get? id = some node ∧ node.bitlen = bits := by
  unfold callInput at ok
  obtain ⟨valid,ok⟩ := check_ok _ _ _ _ ok
  have valid' : (bits = 32 ∨ bits = 128) ∧ query < 2^bits := by simpa using valid
  refine ⟨valid'.1,valid'.2,?_⟩
  intro id atRoot
  subst root
  simp only [] at ok
  obtain ⟨a,addressOk,ok⟩ := bind_ok ok
  obtain ⟨node,decoded,ok⟩ := bind_ok ok
  obtain ⟨width,_⟩ := check_ok _ _ _ _ ok
  have fields := reconstruct_fields related
  simp only [address] at addressOk
  cases found : names.nodes.find? (·.1 == id) with
  | none => rw [found] at addressOk; cases addressOk
  | some pair =>
    rw [found] at addressOk
    have equal : pair.2 = a := Except.ok.inj addressOk
    have identity : pair.1 = id := by simpa using List.find?_some found
    have member := List.mem_of_find?_eq_some found
    obtain ⟨⟨id',n⟩,targetMember,sameId,read⟩ := fields.nodes.left pair member
    have same : n = node := Except.ok.inj (read.symm.trans (equal ▸ mapError_ok decoded))
    obtain ⟨source,present,nodeEq⟩ := target_node targetMember
    refine ⟨source,?_,?_⟩
    · simpa only [←identity,sameId] using present
    · have eq : source.bitlen = node.width := congrArg Node.width (nodeEq.trans same)
      exact eq.trans (eq_of_beq width)

theorem trieHeap_of_checks {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {d : Device} {root : Option NodeId} {bits query : Nat}
    (related : Corresponds names o m d)
    (checked : heap (target d) [d.peerAllowedips.root4,d.peerAllowedips.root6] = .ok ())
    (input : callInput names o m root bits query = .ok ()) :
    AllowedipsRelation.TrieHeap m (interpretation names.nodes) (interpretation names.peers)
      (fun id => d.nodes.get? id) root bits query := by
  have fields := reconstruct_fields related
  obtain ⟨family,bounded,rootWidth⟩ := callInput_ok related input
  have reachable : ∀ id, AllowedipsRelation.Reached (fun id => d.nodes.get? id) root bits query id →
      ∃ node, d.nodes.get? id = some node ∧ node.bitlen = bits := by
    intro id reached
    induction reached with
    | root id atRoot => exact rootWidth id atRoot
    | child id node next reached present matching short link ih =>
      obtain ⟨parent,parentAt,width⟩ := ih
      have same : parent = node := Option.some.inj (parentAt.symm.trans present)
      subst parent
      have member : (id,targetNode node) ∈ (target d).nodes :=
        List.mem_map.mpr ⟨(id,node),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,rfl⟩
      have childMember : some next ∈ (targetNode node).children.toList :=
        by simpa only [targetNode,Array.mem_toList_iff] using Array.mem_of_getElem? link
      obtain ⟨child,found,widthEq⟩ := heap_edges checked id (targetNode node) member next childMember
      obtain ⟨source,present,nodeEq⟩ := target_node found
      exact ⟨source,present,(congrArg Node.width nodeEq).trans (widthEq.trans width)⟩
  refine ⟨family,bounded,?_⟩
  intro id reached
  obtain ⟨node,present,width⟩ := reachable id reached
  obtain ⟨a,member,decoded⟩ := fields.node present
  exact ⟨node,present,decoded_node_fields fields member decoded width bounded⟩

#print axioms heap_edges
#print axioms trieHeap_of_checks
end Binary.Pair.Trie
