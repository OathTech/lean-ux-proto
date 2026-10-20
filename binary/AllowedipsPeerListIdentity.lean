import AllowedipsPeerListEdges
import PairIndexNames

namespace Binary.Pair.Allowedips.Ring

theorem pointer_named {names : List (Nat×Nat)} {path : String} {raw id : Nat}
    (read : Trie.pointer names path raw=.ok (some id)) : (id,raw) ∈ names := by
  unfold Trie.pointer at read
  split at read
  · cases read
  · cases found : names.find? (·.2==raw) with
    | none => rw [found] at read; cases read
    | some pair =>
      rw [found] at read
      have identity : pair.1=id := Option.some.inj (Except.ok.inj read)
      have address : pair.2=raw := by simpa using List.find?_some found
      simpa only [←identity,←address] using List.mem_of_find?_eq_some found

theorem Fields.named {names m head previous link next id} (fields : Fields names m head previous link next id) :
    (id,link-AllowedipsMutationLayout.peer_list) ∈ names.trie.nodes := pointer_named fields.owner

theorem Fields.identity_iff {names m head p link q id p' link' q' id'}
    (left : Fields names m head p link q id) (right : Fields names m head p' link' q' id')
    (unique : (names.trie.nodes.map Prod.fst).Nodup) : id=id' ↔ link=link' := by
  constructor
  · intro same
    have named := right.named
    rw [←same] at named
    have bases := Index.unique_first unique left.named named
    have := left.valid
    have := right.valid
    omega
  · intro same
    subst link'
    exact Option.some.inj (Except.ok.inj (left.owner.symm.trans right.owner))

theorem Chain.erase_ids {names m head previous nodes removed oldPrev oldNext id}
    (shape : Chain names m head previous nodes) (focus : Fields names m head oldPrev removed oldNext id)
    (unique : (names.trie.nodes.map Prod.fst).Nodup) :
    (Ring.erase removed nodes).map Prod.snd=(nodes.map Prod.snd).filter (· != id) := by
  rw [List.filter_map]
  apply congrArg (List.map Prod.snd)
  apply List.filter_congr
  rintro ⟨link,current⟩ member
  obtain ⟨p,q,fields⟩ := shape.member_fields member
  by_cases same : link=removed
  · have identity := (fields.identity_iff focus unique).mpr same
    simp only [Function.comp_apply,same,identity,bne_self_eq_false]
  · have identity : current≠id := fun equal => same ((fields.identity_iff focus unique).mp equal)
    simp only [Function.comp_apply,show (link != removed)=true from by simpa using same,
      show (current != id)=true from by simpa using identity]

#print axioms Chain.erase_ids
end Binary.Pair.Allowedips.Ring
