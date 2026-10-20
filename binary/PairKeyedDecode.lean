import PairLookupFields
import PairLookupSourceFrame

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG Index

theorem Mapped.keys {R : α → β → Prop} {xs : List α} {ys : List β}
    (mapped : Mapped R xs ys) (left : α → κ) (right : β → κ)
    (key : ∀ x y, R x y → left x=right y) : xs.map left=ys.map right := by
  induction mapped with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,key _ _ head,ih]

/-- Rebuild a decoder result from its retained identity ordering and
per-object read equations. This avoids expanding finite maps or whole heaps. -/
theorem mapM_keyed {f : α → Except ε β} {xs : List α} {ys : List β}
    (left : α → κ) (right : β → κ) (keys : xs.map left=ys.map right)
    (read : ∀ x ∈ xs, ∀ y ∈ ys, left x=right y → f x=.ok y) : xs.mapM f=.ok ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at keys
  | cons x xs ih =>
    cases ys with
    | nil => simp at keys
    | cons y ys =>
      obtain ⟨equal,rest⟩ := List.cons.inj keys
      rw [List.mapM_cons,read x (by simp) y (by simp) equal]
      have tail := ih rest (fun a ha b hb eq => read a (by simp [ha]) b (by simp [hb]) eq)
      rw [tail]
      rfl

theorem mapM_values {f : α → Except ε β} {g : α → β} {xs : List α}
    (read : ∀ x ∈ xs, f x=.ok (g x)) : xs.mapM f=.ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,read x (by simp)]
    have tail := ih (fun y member => read y (by simp [member]))
    change (do let values ← xs.mapM f; pure (g x::values))=.ok (g x::xs.map g)
    rw [tail]
    rfl

theorem owner_keys {n o m d} (related : Corresponds n o m d) :
    n.owners.map Prod.fst=(target d).ownerWords.map Prod.fst := by
  apply Mapped.keys (mapM_ok (reconstruct_components related).2.2.1) Prod.fst Prod.fst
  rintro ⟨owner,base⟩ pair decoded
  obtain ⟨_,_,decoded⟩ := bind_ok decoded
  obtain ⟨count,_,done⟩ := bind_ok decoded
  have equal : (owner,count)=pair := Except.ok.inj done
  have keys := congrArg (fun pair : IndexOwner × Option PeerId => pair.1) equal
  exact keys

theorem count_keys {n o m d} (related : Corresponds n o m d) :
    n.peers.map Prod.fst=(target d).refcounts.map Prod.fst := by
  apply Mapped.keys (mapM_ok (reconstruct_components related).2.2.2) Prod.fst Prod.fst
  rintro ⟨id,base⟩ pair decoded
  obtain ⟨count,_,done⟩ := bind_ok decoded
  have equal : (id,count)=pair := Except.ok.inj done
  have keys := congrArg (fun pair : PeerId × Nat => pair.1) equal
  exact keys

theorem SourceFrame.owner_keys {c before after} (frame : SourceFrame c before after) :
    (target after).ownerWords.map Prod.fst=(target before).ownerWords.map Prod.fst := by
  have peers := congrArg (List.map IndexOwner.handshake) frame.peerIds
  have keypairs := congrArg (List.map IndexOwner.keypair) frame.keypairIds
  simp only [List.map_map,Function.comp_def] at peers keypairs
  simp only [target,Id.run,Pure.pure,List.map_append,List.map_map,Function.comp_def]
  rw [peers,keypairs]

theorem SourceFrame.count_keys {c before after} (frame : SourceFrame c before after) :
    (target after).refcounts.map Prod.fst=(target before).refcounts.map Prod.fst := by
  simpa only [target,Id.run,Pure.pure,List.map_map,Function.comp_def] using frame.peerIds

#print axioms mapM_keyed
end Binary.Pair.IndexLookup
