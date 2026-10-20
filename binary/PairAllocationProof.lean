import PairCountUpdate

namespace Binary.Pair.Trie
set_option maxRecDepth 2048

theorem pairwise_mem_ne {R : α → α → Prop} {xs : List α}
    (symmetric : ∀ a b, R a b → R b a) (pairs : xs.Pairwise R)
    {a b : α} (left : a ∈ xs) (right : b ∈ xs) (different : a≠b) : R a b := by
  induction xs with
  | nil => cases left
  | cons x xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp pairs
    rcases List.mem_cons.mp left with rfl | leftTail
    · rcases List.mem_cons.mp right with rfl | rightTail
      · exact False.elim (different rfl)
      · exact head b rightTail
    · rcases List.mem_cons.mp right with rfl | rightTail
      · exact symmetric _ _ (head a leftTail)
      · exact ih tail leftTail rightTail

theorem validate_pairwise {names : Names} {o : AllowedipsProbe.Offsets}
    (checked : validate names o = .ok ()) :
    (names.nodes.map (fun (pair : Nat×Nat) => (pair.2,o.nodeSize)) ++
      names.peers.map (fun (pair : Nat×Nat) => (pair.2,Layouts.peerSize))).Pairwise
        (fun a b : Span => disjointRanges a.1 a.2 b.1 b.2 = true) := by
  unfold validate at checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,rangesOk,_⟩ := bind_ok checked
  let ranges : List Span := names.nodes.map (fun (pair : Nat×Nat) => (pair.2,o.nodeSize)) ++ names.peers.map (fun (pair : Nat×Nat) => (pair.2,Layouts.peerSize))
  have each := forIn_ok (P := fun entry : (Nat×Nat)×Nat =>
      ∀ other ∈ ranges.drop (entry.2+1), disjointRanges entry.1.1 entry.1.2 other.1 other.2 = true)
    (fun entry _ before after run => by
      obtain ⟨_,run⟩ := check_ok _ _ _ _ run
      obtain ⟨_,inner,run⟩ := bind_ok run
      refine ⟨(),(Except.ok.inj run).symm,?_⟩
      exact forIn_ok (fun other _ before after run => by
        obtain ⟨apart,run⟩ := check_ok _ _ _ _ run
        exact ⟨(),(Except.ok.inj run).symm,apart⟩) inner) rangesOk
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less
  change i < ranges.length at hi
  change j < ranges.length at hj
  have member : (ranges[i],i) ∈ ranges.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  exact each _ member _ (List.mem_drop_iff_getElem.mpr ⟨j-(i+1),by omega,by congr 1; omega⟩)

/-- Separation of peer allocations is already an executable validation
clause. Different source identities cannot share their count bytes. -/
theorem peer_allocations_apart {names : Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {s : State}
    (checked : reconstruct names o m = .ok s) {id other base otherBase : Nat}
    (left : (id,base) ∈ names.peers) (right : (other,otherBase) ∈ names.peers) (different : id≠other) :
    disjointRanges base Layouts.peerSize otherBase Layouts.peerSize = true := by
  unfold reconstruct at checked
  obtain ⟨result,validated,_⟩ := bind_ok checked
  cases result
  have pairs := (List.pairwise_append.mp (validate_pairwise validated)).2.1
  have named := List.pairwise_map.mp pairs
  apply pairwise_mem_ne (R := fun a b : Nat×Nat => disjointRanges a.2 Layouts.peerSize b.2 Layouts.peerSize = true)
    (fun a b h => by simpa only [disjointRanges,Bool.or_comm] using h) named left right
  intro equal
  exact different (congrArg Prod.fst equal)

theorem other_count_separate {names : Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {s : State}
    (checked : reconstruct names o m = .ok s) {id other base otherBase : Nat}
    (left : (id,base) ∈ names.peers) (right : (other,otherBase) ∈ names.peers) (different : id≠other) :
    ∀ a, InRange (.ofNat 64 (base+o.peerRefcount)) 4 a →
      ¬InRange (.ofNat 64 (otherBase+o.peerRefcount)) 4 a := by
  have fields := reconstruct_fields checked
  have leftBound := fields.peerRange id base left
  have rightBound := fields.peerRange other otherBase right
  have apart := peer_allocations_apart checked left right different
  have numeric : base+Layouts.peerSize ≤ otherBase ∨ otherBase+Layouts.peerSize ≤ base := by
    simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using apart
  have layout := fields.layout.2.2.2.2.2.2.2.2
  have fieldBound : o.peerRefcount+4 ≤ Layouts.peerSize := by rw [layout]; decide
  intro a first second
  have firstRange := Span.location (span := (base+o.peerRefcount,4)) (by omega) first
  have secondRange := Span.location (span := (otherBase+o.peerRefcount,4)) (by omega) second
  rcases numeric with h | h <;> omega

#print axioms other_count_separate
end Binary.Pair.Trie
