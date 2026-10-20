import AllowedipsTrieEdgeFacts

namespace Binary.Pair.Trie
open Leanux Leanux.WG

theorem edgeStep_resources {s roots id node edge before after}
    (run : edgeStep s roots id node edge before=.ok after) :
    after=.yield (edgeChildren edge++before) ∧ ∀ next ∈ edgeChildren edge, next ∉ before := by
  have facts := (edgeStep_facts run).2
  have absent : ∀ next ∈ edgeChildren edge, next ∉ before := by
    rcases edge with ⟨child,bit⟩
    cases child with
    | none => simp [edgeChildren]
    | some next =>
      obtain ⟨child,found,_⟩ := facts next rfl
      have fresh : next ∉ before := by
        intro member
        have seen : before.contains next=true := by simpa using member
        simp only [edgeStep,found,seen,ite_true] at run
        cases run
      simpa [edgeChildren] using fresh
  exact ⟨Except.ok.inj (run.symm.trans (edgeStep_of_facts facts absent)),absent⟩

/-- A list of valid edges executes the existing duplicate-parent guard when
the new and previously visited children are jointly distinct. -/
theorem edgeWalk_of_facts {s roots id node} {edges : List (Option NodeId×Nat)} {before : List NodeId}
    (valid : ∀ edge ∈ edges, EdgeFacts s roots node edge)
    (distinct : (edges.flatMap edgeChildren++before).Nodup) :
    forIn edges before (edgeStep s roots id node)=.ok ((edges.flatMap edgeChildren).reverse++before) := by
  induction edges generalizing before with
  | nil => rfl
  | cons edge edges ih =>
    have later := fun e member => valid e (List.mem_cons_of_mem edge member)
    rcases edge with ⟨child,bit⟩
    cases child with
    | none =>
      simp only [List.flatMap_cons,edgeChildren,Option.toList_none,List.nil_append] at distinct ⊢
      rw [List.forIn_cons,edgeStep_of_facts (valid _ (by simp)) (by simp [edgeChildren])]
      exact ih later distinct
    | some next =>
      have distinct : (next::(edges.flatMap edgeChildren++before)).Nodup := by
        simpa only [List.flatMap_cons,edgeChildren,Option.toList_some,List.cons_append,List.nil_append] using distinct
      have absent : next ∉ before := fun member => (List.nodup_cons.mp distinct).1 (List.mem_append_right _ member)
      have nextDistinct : (edges.flatMap edgeChildren++next::before).Nodup := List.perm_middle.symm.nodup distinct
      rw [List.forIn_cons,edgeStep_of_facts (valid _ (by simp)) (by simpa [edgeChildren] using absent)]
      dsimp only [Bind.bind,Except.bind]
      have result := ih later nextDistinct
      simpa only [List.flatMap_cons,edgeChildren,Option.toList_some,List.cons_append,List.nil_append,
        List.reverse_cons,List.append_assoc,List.singleton_append] using result

/-- Successful traversal exports the distinctness enforced by the same guard;
this supplies old-heap facts before proving a structural mutation. -/
theorem edgeWalk_nodup {s roots id node} {edges : List (Option NodeId×Nat)} {before after : List NodeId}
    (initial : before.Nodup) (run : forIn edges before (edgeStep s roots id node)=.ok after) :
    (edges.flatMap edgeChildren++before).Nodup := by
  induction edges generalizing before with
  | nil => exact initial
  | cons edge edges ih =>
    rw [List.forIn_cons] at run
    obtain ⟨step,first,run⟩ := bind_ok run
    obtain ⟨rfl,absent⟩ := edgeStep_resources first
    rcases edge with ⟨child,bit⟩
    cases child with
    | none =>
      simp only [edgeChildren,Option.toList_none,List.nil_append] at run
      simpa only [List.flatMap_cons,edgeChildren,Option.toList_none,List.nil_append] using ih initial run
    | some next =>
      have notBefore : next ∉ before := absent next (by simp [edgeChildren])
      have nextInitial : (next::before).Nodup := List.nodup_cons.mpr ⟨notBefore,initial⟩
      have nextRun : forIn edges (next::before) (edgeStep s roots id node)=.ok after := run
      have distinct := ih nextInitial nextRun
      have moved := List.perm_middle.nodup distinct
      simpa only [List.flatMap_cons,edgeChildren,Option.toList_some,List.cons_append,List.nil_append] using moved

#print axioms edgeWalk_of_facts
#print axioms edgeWalk_nodup
end Binary.Pair.Trie
