import AllowedipsAllocationReconstruct
import Leanux.Proofs.WG.AllowedIps.MutationMirror

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG
open Leanux.Proofs.WG.AllowedIps

/-- An allocation frontier larger than every existing identity makes the
physical naming append agree with the mirror's ordered map insertion. -/
theorem tree_insert_max (nodes : Std.TreeMap Nat α) (id : Nat) (node : α)
    (below : ∀ pair ∈ nodes.toList, pair.1<id) :
    (nodes.insert id node).toList=nodes.toList++[(id,node)] := by
  have unchanged : nodes.toList.filter (fun p => decide (¬(id==p.1)=true))=nodes.toList := by
    apply List.filter_eq_self.mpr
    intro p present
    have different := Nat.ne_of_gt (below p present)
    simpa using different
  have permutation := Std.TreeMap.toList_insert_perm (t:=nodes) (k:=id) (v:=node)
  rw [unchanged] at permutation
  have moved : ((id,node)::nodes.toList).Perm (nodes.toList++[(id,node)]) := by
    exact List.perm_append_comm (l₁:=[(id,node)]) (l₂:=nodes.toList)
  let ordered := fun a b : Nat×α => a=b ∨ a.1<b.1
  have oldOrder : nodes.toList.Pairwise ordered :=
    (Std.TreeMap.ordered_keys_toList (t:=nodes)).imp (fun h => .inr (Nat.compare_eq_lt.mp h))
  have newOrder : (nodes.insert id node).toList.Pairwise ordered :=
    (Std.TreeMap.ordered_keys_toList (t:=nodes.insert id node)).imp (fun h => .inr (Nat.compare_eq_lt.mp h))
  have appended : (nodes.toList++[(id,node)]).Pairwise ordered := by
    rw [List.pairwise_append]
    refine ⟨oldOrder,by simp,?_⟩
    intro a present b singleton
    have equal : b=(id,node) := by simpa using singleton
    rw [equal]
    exact .inr (below a present)
  exact List.Perm.eq_of_pairwise (le:=ordered)
    (fun a b _ _ forward backward => by
      rcases forward with same|less
      · exact same
      · rcases backward with same|greater
        · exact same.symm
        · exact False.elim (Nat.lt_asymm less greater)) newOrder appended (permutation.trans moved)

def appendOwner (id pid : Nat) (entry : PeerId×Nat×List NodeId) : PeerId×Nat×List NodeId :=
  (entry.1,entry.2.1,if entry.1=pid then entry.2.2++[id] else entry.2.2)

def installedRoot (v4 : Bool) (key cidr pid : Nat) (s : State) : State :=
  { table := if v4 then {s.table with root4:=some s.nextNode} else {s.table with root6:=some s.nextNode}
    nodes := s.nodes++[(s.nextNode,{newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4})]
    peers := s.peers.map (appendOwner s.nextNode pid)
    nextNode := s.nextNode+1 }

theorem target_emptyInstalled (d : Device) (v4 : Bool) (key cidr pid : Nat) (owner : Peer)
    (hasPeer : d.peers.get? pid=some owner)
    (below : ∀ pair ∈ d.nodes.toList, pair.1<d.nextNode) :
    target (emptyInstalled d v4 key cidr pid owner)=installedRoot v4 key cidr pid (target d) := by
  have nodes : (emptyInstalled d v4 key cidr pid owner).nodes.toList=
      d.nodes.toList++[(d.nextNode,{newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4})] := by
    simp only [emptyInstalled,rootWrite]
    have overwritten : ((d.nodes.insert d.nextNode (newNode key cidr (rootWidth v4) (some pid))).insert d.nextNode
        {newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4}).Equiv
        (d.nodes.insert d.nextNode {newNode key cidr (rootWidth v4) (some pid) with parent:=rootSlot v4}) := by
      apply Std.TreeMap.Equiv.of_forall_constGet?_eq
      intro current
      by_cases same : d.nextNode=current <;> simp [Std.TreeMap.getElem?_insert,same]
    rw [overwritten.toList_eq,tree_insert_max d.nodes d.nextNode _ below]
  have peers : (emptyInstalled d v4 key cidr pid owner).peers.toList=
      d.peers.toList.map (fun (current,p) =>
        (current,if current=pid then {owner with allowedipsList:=owner.allowedipsList++[d.nextNode]} else p)) := by
    simp only [emptyInstalled,rootWrite]
    exact Trie.tree_insert_present d.peers pid owner _ hasPeer
  have peerProjection : ((emptyInstalled d v4 key cidr pid owner).peers.toList.map
      (fun (id,p) => (id,p.refcount,p.allowedipsList)))=
      (target d).peers.map (appendOwner d.nextNode pid) := by
    rw [peers]
    simp only [target]
    simp only [List.map_map]
    apply List.map_congr_left
    rintro ⟨current,p⟩ present
    by_cases same : current=pid
    · subst current
      have equal := Option.some.inj ((Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp present).symm.trans hasPeer)
      subst owner
      simp [appendOwner]
    · simp [appendOwner,same]
  have tableEq : (emptyInstalled d v4 key cidr pid owner).peerAllowedips=
      if v4 then {d.peerAllowedips with root4:=some d.nextNode}
      else {d.peerAllowedips with root6:=some d.nextNode} := by
    cases v4 <;> rfl
  have nextEq : (emptyInstalled d v4 key cidr pid owner).nextNode=d.nextNode+1 := rfl
  simp only [target] at peerProjection
  simp only [target,installedRoot,tableEq,nextEq,nodes,peerProjection]

#print axioms tree_insert_max
#print axioms target_emptyInstalled
end Binary.Pair.Allowedips
