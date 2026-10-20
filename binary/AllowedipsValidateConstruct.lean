import AllowedipsAllocationNames

namespace Binary.Pair.Allowedips

/-- A unit traversal succeeds when every visited body yields. Used to prove
existing executable validation, without adding a second checker. -/
theorem forIn_yield {xs : List α} {f : α → Unit → Except ε (ForInStep Unit)}
    (each : ∀ x ∈ xs, f x ()=.ok (.yield ())) : forIn xs () f=.ok () := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons,each x (by simp)]
    exact ih (fun y present => each y (List.mem_cons_of_mem x present))

theorem eraseDups_of_nodup [BEq α] [LawfulBEq α] {xs : List α}
    (unique : xs.Nodup) : xs.eraseDups=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp unique
    have keep : xs.filter (fun y => !y==x)=xs := by
      apply List.filter_eq_self.mpr
      intro y present
      have different : y≠x := by intro equal; exact absent (equal ▸ present)
      simp [different]
    rw [List.eraseDups_cons,keep,ih tail]

/-- Construct the existing trie interpretation check from its ordinary
layout, identity and allocation facts. No memory or desired post-state is a
premise. The range iteration is proved from pairwise ownership. -/
theorem trie_validate_construct {names : Trie.Names} {o : AllowedipsProbe.Offsets}
    (layout : (o.nodeSize==AllowedipsLayout.nodeSize && o.peer==AllowedipsLayout.peer &&
      o.children==AllowedipsLayout.bit && o.cidr==AllowedipsLayout.cidr &&
      o.bitAtA==AllowedipsLayout.bit_at_a && o.bitAtB==AllowedipsLayout.bit_at_b &&
      o.bitlen==AllowedipsLayout.bitlen && o.bits==AllowedipsLayout.bits &&
      o.peerRefcount==Layouts.peer_refcount)=true)
    (unique : ∀ pairs ∈ [names.nodes,names.peers],
      (pairs.map Prod.fst).Nodup ∧ (pairs.map Prod.snd).Nodup)
    (bounded : ∀ span ∈ names.nodes.map (fun p => (p.2,o.nodeSize))++names.peers.map (fun p => (p.2,Layouts.peerSize)),
      0<span.1 ∧ span.1+span.2<2^64)
    (apart : (names.nodes.map (fun p => (p.2,o.nodeSize))++names.peers.map (fun p => (p.2,Layouts.peerSize))).Pairwise
      (fun a b => disjointRanges a.1 a.2 b.1 b.2=true)) : Trie.validate names o=.ok () := by
  unfold Trie.validate
  apply check_of _ _ _ _ layout
  have namesRun : (forIn (m:=Decode) [names.nodes,names.peers] () (fun (pairs : List (Nat×Nat)) _ => do
      unless (pairs.map Prod.fst).eraseDups.length==pairs.length &&
        (pairs.map Prod.snd).eraseDups.length==pairs.length do
          throw (⟨"interpretation",0,"duplicate identity/address"⟩ : DecodeError)
      pure (.yield ())))=.ok () := by
    apply forIn_yield
    intro pairs member
    have checks := unique pairs member
    simp only [eraseDups_of_nodup checks.1,eraseDups_of_nodup checks.2,List.length_map,
      beq_self_eq_true,Bool.and_self,ite_true]
    rfl
  rw [namesRun]
  let ranges := names.nodes.map (fun p => (p.2,o.nodeSize))++names.peers.map (fun p => (p.2,Layouts.peerSize))
  change ranges.Pairwise (fun a b => disjointRanges a.1 a.2 b.1 b.2=true) at apart
  have rangesRun : (forIn (m:=Decode) ranges.zipIdx () (fun (entry : Span×Nat) _ => do
      unless 0<entry.1.1 && entry.1.1+entry.1.2<2^64 do
        throw (⟨"interpretation",entry.1.1,"NULL/wrapping object"⟩ : DecodeError)
      for other in ranges.drop (entry.2+1) do
        unless disjointRanges entry.1.1 entry.1.2 other.1 other.2 do
          throw (⟨"interpretation",entry.1.1,"overlapping objects"⟩ : DecodeError)
      pure (.yield ())))=.ok () := by
    apply forIn_yield
    rintro ⟨span,i⟩ member
    obtain ⟨small,atIndex⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp member)
    have spanMember : span ∈ ranges := atIndex ▸ List.getElem_mem small
    have bounds := bounded span spanMember
    apply check_of _ _ _ _ (by simpa only [Bool.and_eq_true,decide_eq_true_eq] using bounds)
    have later : forIn (m:=Decode) (ranges.drop (i+1)) () (fun (other : Span) _ => do
        unless disjointRanges span.1 span.2 other.1 other.2 do
          throw (⟨"interpretation",span.1,"overlapping objects"⟩ : DecodeError)
        pure (.yield ()))=.ok () := by
      apply forIn_yield
      intro other present
      obtain ⟨j,bound,position⟩ := List.mem_drop_iff_getElem.mp present
      have separated := List.pairwise_iff_getElem.mp apart i (i+1+j) small (by omega) (by omega)
      rw [atIndex,position] at separated
      simp only [separated,ite_true]
      rfl
    rw [later]
    rfl
  change (do
    let _ ← forIn (m:=Decode) ranges.zipIdx () _
    pure ())=.ok ()
  rw [rangesRun]
  rfl

#print axioms trie_validate_construct
end Binary.Pair.Allowedips
