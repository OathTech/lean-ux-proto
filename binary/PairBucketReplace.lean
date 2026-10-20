import PairIndexNames

namespace Binary.Pair.Index
open Leanux Leanux.WG

def replaceOwner (old new : IndexOwner) (e : IndexEntry) : IndexEntry :=
  if e.owner==old then {e with owner := new} else e

def replaceNodes (old new : Nat) (oldOwner newOwner : IndexOwner) (nodes : Nodes) : Nodes :=
  nodes.map fun (link,e) => (skip old new link,replaceOwner oldOwner newOwner e)

theorem replace_head (old new : Nat) (oldOwner newOwner : IndexOwner) (nodes : Nodes)
    (nonzero : old≠0) :
    head (replaceNodes old new oldOwner newOwner nodes)=skip old new (head nodes) := by
  cases nodes
  · simp [replaceNodes,head,skip,Ne.symm nonzero]
  · rfl

theorem skip_offset (old new value offset : Nat) :
    skip (old+offset) (new+offset) (value+offset)=skip old new value+offset := by
  by_cases equal : value=old
  · simp [equal,skip]
  · simp [skip,equal]

/-- A segment may replace a node without relating its intermediate stores.
Once its local field equations are proved, the old finite chain gives the
new finite chain at the correspondence point. -/
theorem Chain.replace {n o before after b previous nodes old new oldOwner newOwner}
    (shape : Chain n o before b previous nodes) (nonzero : old≠0)
    (updated : ∀ link current prev next, (link,current) ∈ nodes →
      NodeFields n o before b link prev next current →
      NodeFields n o after b (skip old new link)
        (skip (old+o.next) (new+o.next) prev) (skip old new next)
        (replaceOwner oldOwner newOwner current)) :
    Chain n o after b (skip (old+o.next) (new+o.next) previous)
      (replaceNodes old new oldOwner newOwner nodes) := by
  induction shape with
  | nil => exact .nil _
  | @cons previous link current rest fields tail ih =>
    have field := updated link current previous (head rest) (by simp) fields
    rw [←replace_head old new oldOwner newOwner rest nonzero] at field
    have tail := ih (fun l e p q member => updated l e p q (by simp [member]))
    rw [skip_offset] at tail
    exact .cons field tail

theorem skip_injective_on {old new : Nat} {values : List Nat} (absent : new ∉ values)
    {x y : Nat} (xm : x ∈ values) (ym : y ∈ values)
    (equal : skip old new x=skip old new y) : x=y := by
  unfold skip at equal
  split at equal <;> split at equal <;> simp_all

theorem replace_distinct {old new oldOwner newOwner nodes}
    (distinct : (nodes.map Prod.fst).Nodup) (absent : new ∉ nodes.map Prod.fst) :
    ((replaceNodes old new oldOwner newOwner nodes).map Prod.fst).Nodup := by
  have mapped : ((replaceNodes old new oldOwner newOwner nodes).map Prod.fst)=
      (nodes.map Prod.fst).map (skip old new) := by simp [replaceNodes,List.map_map,Function.comp_def]
  rw [mapped]
  apply List.pairwise_map.mpr
  exact distinct.imp_of_mem (fun xm ym different equal => different (skip_injective_on absent xm ym equal))

#print axioms Chain.replace
#print axioms replace_distinct
end Binary.Pair.Index
