import AllowedipsExactSource

namespace Binary.Pair.Trie
open Leanux Leanux.WG

/-- The structural trie assertion does not observe peer ownership. -/
theorem heap_mapPeer (s : State) (roots : List (Option NodeId))
    (f : NodeId → Option PeerId → Option PeerId) :
    heap {s with nodes := s.nodes.map (fun (id,n) => (id,{n with peer := f id n.peer}))} roots=
      heap s roots := by
  simp only [heap,List.forIn_map,List.any_map,List.find?_map,Function.comp_def]
  congr 1
  funext parents
  congr 1
  congr 1
  funext entry previous
  rcases entry with ⟨id,node⟩
  dsimp only
  congr 1
  congr 1
  funext child before
  rcases child with ⟨child,bit⟩
  cases child with
  | none => rfl
  | some next =>
    dsimp only
    cases found : s.nodes.find? (fun entry => entry.1==next) with
    | none => rfl
    | some entry => rcases entry with ⟨childId,n⟩; rfl

#print axioms heap_mapPeer
end Binary.Pair.Trie
