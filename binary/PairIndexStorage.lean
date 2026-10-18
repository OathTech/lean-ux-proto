import PairSpan

namespace Binary.Pair.Index

/-- Physical storage used by the index subsystem. The table is one span,
so checking its separation does not enumerate all pairs of bucket heads. -/
def storageSpans (n : Names) (o : Offsets) : List Span :=
  (n.table,o.tableSize)::
    (n.owners.map (fun (_,base) => (base,o.entrySize)) ++
      n.peers.map (fun (_,base) => (base+o.peerRefcount,4)))

def separated : List Span → Bool
  | [] => true
  | span::rest => rest.all (fun other => disjointRanges span.1 span.2 other.1 other.2) && separated rest

/-- Immutable physical readiness for later stores. It checks entry storage
and peer counts, including an entry embedded in its own peer. It imposes no
condition on table membership, peer-word values or reference counts. -/
def storageCheck (n : Names) (o : Offsets) : Bool :=
  let spans := storageSpans n o
  spans.all (fun s => 0 < s.2 && s.1+s.2 ≤ 2^64) && separated spans

theorem separated_sound {spans : List Span} (checked : separated spans=true) :
    spans.Pairwise (fun a b => disjointRanges a.1 a.2 b.1 b.2=true) := by
  induction spans with
  | nil => exact .nil
  | cons span rest ih =>
    have parts : rest.all (fun other => disjointRanges span.1 span.2 other.1 other.2)=true ∧
        separated rest=true := by simpa only [separated,Bool.and_eq_true] using checked
    exact .cons (List.all_eq_true.mp parts.1) (ih parts.2)

theorem storage_bounds {n o} (checked : storageCheck n o=true) {span : Span}
    (member : span ∈ storageSpans n o) : 0 < span.2 ∧ span.1+span.2≤2^64 := by
  have all : (storageSpans n o).all (fun s => 0 < s.2 && s.1+s.2 ≤ 2^64)=true := by
    exact (show _ ∧ _ from by simpa only [storageCheck,Bool.and_eq_true] using checked).1
  simpa only [Bool.and_eq_true,decide_eq_true_eq] using List.all_eq_true.mp all span member

theorem table_storage (n : Names) (o : Offsets) : (n.table,o.tableSize) ∈ storageSpans n o := by
  simp [storageSpans]

theorem entry_storage {n : Names} {o : Offsets} {owner base}
    (named : (owner,base) ∈ n.owners) : (base,o.entrySize) ∈ storageSpans n o := by
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨(owner,base),named,rfl⟩))

theorem count_storage {n : Names} {o : Offsets} {id base}
    (named : (id,base) ∈ n.peers) : (base+o.peerRefcount,4) ∈ storageSpans n o := by
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩))

end Binary.Pair.Index
