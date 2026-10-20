import AllowedipsReconstructed

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

def owners (s : State) (id : NodeId) : List PeerId :=
  s.peers.flatMap fun (pid,_,xs) => xs.filterMap fun x => if x==id then some pid else none

theorem heap_ownership {names s m} (checked : heap names s m=.ok ()) :
    ∀ id node, (id,node) ∈ s.nodes → owners s id=node.peer.toList ∧
      (node.peer=none → internalListCheck names m id=.ok ()) := by
  unfold heap at checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,loop,_⟩ := bind_ok checked
  have all := forIn_ok (P := fun pair : NodeId×AipNode =>
    owners s pair.1=pair.2.peer.toList ∧ (pair.2.peer=none → internalListCheck names m pair.1=.ok ()))
    (fun pair _ before after run => by
      obtain ⟨incoming,_,run⟩ := bind_ok run
      obtain ⟨incoming,_,run⟩ := bind_ok run
      obtain ⟨_,run⟩ := check_ok _ _ _ _ run
      obtain ⟨membership,run⟩ := check_ok _ _ _ _ run
      have equal : owners s pair.1=pair.2.peer.toList := by simpa only [owners,beq_iff_eq] using membership
      by_cases internal : pair.2.peer=none
      · simp only [internal,Option.isNone_none,ite_true] at run
        obtain ⟨value,read,run⟩ := bind_ok run
        cases value
        exact ⟨before,(Except.ok.inj run).symm,equal,fun _ => read⟩
      · have nonnull : pair.2.peer.isNone=false := by cases h : pair.2.peer <;> simp_all
        simp only [nonnull,Bool.false_eq_true,ite_false] at run
        exact ⟨before,(Except.ok.inj run).symm,equal,fun impossible => False.elim (internal impossible)⟩) loop
  intro id node member
  exact all (id,node) member

theorem owners_some {s id pid} (equal : owners s id=[pid]) :
    ∃ count entries, (pid,count,entries) ∈ s.peers ∧ id ∈ entries := by
  have present : pid ∈ owners s id := by rw [equal]; simp
  obtain ⟨⟨current,count,entries⟩,member,found⟩ := List.mem_flatMap.mp present
  obtain ⟨x,atList,value⟩ := List.mem_filterMap.mp found
  by_cases same : x=id
  · simp only [same,beq_self_eq_true,ite_true,Option.some.injEq] at value
    exact ⟨count,entries,value ▸ member,same ▸ atList⟩
  · simp [same] at value

#print axioms heap_ownership
#print axioms owners_some
end Binary.Pair.Allowedips
