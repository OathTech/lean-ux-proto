import PairBucketShape

namespace Binary.Pair.Index
open Leanux Leanux.WG

def erase (removed : Nat) (nodes : Nodes) : Nodes := nodes.filter (fun node => node.1 != removed)

def skip (removed next value : Nat) : Nat := if value=removed then next else value

theorem erase_absent {removed : Nat} {nodes : Nodes}
    (absent : removed ∉ nodes.map Prod.fst) : erase removed nodes=nodes := by
  apply List.filter_eq_self.mpr
  intro node member
  have ne : node.1≠removed := by
    intro equal
    exact absent (List.mem_map.mpr ⟨node,member,equal⟩)
  simpa using ne

theorem Chain.head_erase {n o m b focusB previous nodes removed removedPrevious removedNext entry}
    (shape : Chain n o m b previous nodes)
    (focus : NodeFields n o m focusB removed removedPrevious removedNext entry)
    (distinct : (nodes.map Prod.fst).Nodup) :
    head (erase removed nodes) = skip removed removedNext (head nodes) := by
  cases shape with
  | nil => simp [Index.erase,head,skip,Ne.symm focus.nonzero]
  | @cons previous link current rest fields tail =>
    by_cases same : link=removed
    · subst link
      have nd := List.nodup_cons.mp distinct
      have unchanged := erase_absent nd.1
      have next : head rest=removedNext := word_values fields.forward focus.forward
      simp only [Index.erase,List.filter_cons,show (removed != removed)=false from by simp,Bool.false_eq_true,↓reduceIte]
      change head (erase removed rest) = skip removed removedNext removed
      rw [unchanged,next]
      simp [skip]
    · simp only [Index.erase,List.filter_cons,show (link != removed)=true from by simpa using same,
        ↓reduceIte]
      simp [head,skip,same]

theorem Chain.frame {n o before after b previous nodes}
    (shape : Chain n o before b previous nodes)
    (fields : ∀ link entry oldPrevious oldNext, (link,entry) ∈ nodes →
      NodeFields n o before b link oldPrevious oldNext entry →
      NodeFields n o after b link oldPrevious oldNext entry) :
    Chain n o after b previous nodes := by
  induction shape with
  | nil => exact .nil _
  | cons first tail ih =>
    exact .cons (fields _ _ _ _ (by simp) first)
      (ih (fun link entry prev next member => fields link entry prev next (by simp [member])))

/-- Delete a node using local before/after word equations. The updated fields
will be derived from the actual unlink stores and their byte frame. This
lemma performs the structural induction once, including head and tail cases. -/
theorem Chain.erase {n o before after b focusB previous nodes removed removedPrevious removedNext entry}
    (shape : Chain n o before b previous nodes)
    (focus : NodeFields n o before focusB removed removedPrevious removedNext entry)
    (distinct : (nodes.map Prod.fst).Nodup)
    (updated : ∀ link current oldPrevious oldNext, (link,current) ∈ nodes → link≠removed →
      NodeFields n o before b link oldPrevious oldNext current →
      NodeFields n o after b link (skip (removed+o.next) removedPrevious oldPrevious)
        (skip removed removedNext oldNext) current) :
    Chain n o after b (skip (removed+o.next) removedPrevious previous) (erase removed nodes) := by
  induction shape with
  | nil => exact .nil _
  | @cons previous link current rest first tail ih =>
    have nd := List.nodup_cons.mp distinct
    have updatedRest := fun link current prev next member =>
      updated link current prev next (List.mem_cons_of_mem _ member)
    have restShape := ih nd.2 updatedRest
    by_cases same : link=removed
    · subst link
      have prev : previous=removedPrevious := word_values first.back focus.back
      simpa only [Index.erase,List.filter_cons,show (removed != removed)=false from by simp,Bool.false_eq_true,
        ↓reduceIte,skip,prev,ite_self] using restShape
    · have next := tail.head_erase focus nd.2
      have newFields := updated link current previous (head rest) (by simp) same first
      rw [←next] at newFields
      have different : link+o.next≠removed+o.next := by omega
      have samePrevious : skip (removed+o.next) removedPrevious (link+o.next)=link+o.next := ite_eq_right different
      rw [samePrevious] at restShape
      simpa only [Index.erase,List.filter_cons,show (link != removed)=true from by simpa using same,↓reduceIte]
        using Chain.cons newFields restShape

/-- Return to the exact executable bucket decoder after a proved splice.
The caller supplies local word effects, not successful future decoding. -/
theorem bucket_erase {n o before after b focusB fuel link previous seen entries removed removedPrevious removedNext entry}
    (decoded : bucket n o before b fuel link previous seen=.ok entries)
    (focus : NodeFields n o before focusB removed removedPrevious removedNext entry)
    (updated : ∀ nodes : Nodes, entries=nodes.map Prod.snd → link=head nodes →
      Chain n o before b previous nodes →
      ∀ addr current oldPrevious oldNext, (addr,current) ∈ nodes → addr≠removed →
        NodeFields n o before b addr oldPrevious oldNext current →
        NodeFields n o after b addr (skip (removed+o.next) removedPrevious oldPrevious)
          (skip removed removedNext oldNext) current) :
    ∃ nodes : Nodes, entries=nodes.map Prod.snd ∧ link=head nodes ∧
      Chain n o before b previous nodes ∧
      bucket n o after b fuel (skip removed removedNext link)
        (skip (removed+o.next) removedPrevious previous) seen =
          .ok ((erase removed nodes).map Prod.snd) := by
  obtain ⟨nodes,entriesEq,headEq,shape,length,distinct,fresh⟩ := bucket_shape decoded
  have erased := shape.erase focus distinct (updated nodes entriesEq headEq shape)
  have newDistinct : ((erase removed nodes).map Prod.fst).Nodup := by
    exact distinct.sublist (List.Sublist.map Prod.fst (List.filter_sublist))
  have newFresh : ∀ p ∈ (erase removed nodes).map Prod.fst, p ∉ seen := by
    intro p member
    exact fresh p (List.Sublist.subset (List.Sublist.map Prod.fst (List.filter_sublist)) member)
  have ready := erased.decode fuel seen (Nat.le_trans (List.length_filter_le _ _) length) newDistinct newFresh
  rw [shape.head_erase focus distinct,←headEq] at ready
  exact ⟨nodes,entriesEq,headEq,shape,ready⟩

#print axioms bucket_erase
end Binary.Pair.Index
