import PairAllowedipsNames
import AllowedipsPeerListShape

namespace Binary.Pair.Allowedips

/-- Appending a newly allocated identity preserves every already resolved
pointer. Freshness is needed to validate the extended interpretation and to
resolve the new pointer, not to preserve a successful old first-match lookup. -/
theorem pointer_suffix {names extra path address id}
    (read : Trie.pointer names path address=.ok id) :
    Trie.pointer (names++extra) path address=.ok id := by
  unfold Trie.pointer at read ⊢
  by_cases zero : (address==0)=true
  · simpa only [zero,ite_true] using read
  · simp only [zero] at read ⊢
    cases found : names.find? (·.2==address) with
    | none => simp only [found] at read; cases read
    | some pair => simpa [List.find?_append,found] using read

theorem pointer_allocated {names : Names} {address : Nat} (path : String)
    (nonnull : address≠0) (fresh : ∀ p ∈ names.trie.nodes, p.2≠address) :
    Trie.pointer (names.allocated address).trie.nodes path address=.ok (some names.nextNode) := by
  have absent : names.trie.nodes.find? (·.2==address)=none := by
    apply List.find?_eq_none.mpr
    intro p present
    simpa only [beq_iff_eq] using fresh p present
  simp [Trie.pointer,Names.allocated,nonnull,List.find?_append,absent]

namespace Ring

theorem Fields.allocate {names m head previous link next id address}
    (fields : Fields names m head previous link next id) :
    Fields (names.allocated address) m head previous link next id := by
  refine ⟨?_,fields.notHead,fields.valid,?_,fields.back,fields.forward⟩
  · simp only [Names.allocated,List.any_append,fields.known,Bool.true_or]
  · exact pointer_suffix fields.owner

theorem Chain.allocate {names m head previous nodes address}
    (shape : Chain names m head previous nodes) :
    Chain (names.allocated address) m head previous nodes := by
  induction shape with
  | nil back => exact .nil back
  | cons fields _ ih => exact .cons fields.allocate ih

/-- Adding one allocation increases the runner's existing traversal budget
and preserves every decoded old list, without a new fuel hypothesis. -/
theorem peerList_allocate {names m head previous first entries address}
    (decoded : peerList names m head (names.trie.nodes.length+1) first previous []=.ok entries) :
    peerList (names.allocated address) m head ((names.allocated address).trie.nodes.length+1)
      first previous []=.ok entries := by
  obtain ⟨nodes,entriesEq,firstEq,shape,length,distinct,fresh⟩ := peerList_shape decoded
  rw [entriesEq,firstEq]
  apply shape.allocate.decode _ [] _ distinct fresh
  simpa only [Names.allocated,List.length_append,List.length_cons,List.length_nil] using
    Nat.lt_trans length (Nat.lt_succ_self (names.trie.nodes.length+1))

end Ring

#print axioms pointer_suffix
#print axioms Ring.peerList_allocate
end Binary.Pair.Allowedips
