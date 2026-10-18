import PairBucketErase
import PairCountUpdate

namespace Binary.Pair.Index
open Leanux Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f) = f value := rfl

theorem collect_eq_mapM (f : α → Except ε β) (xs : List α) (initial : Array β) :
    (forIn xs initial fun x acc => do
      let value ← f x
      pure (.yield (acc.push value))) =
      (xs.mapM f).map (fun values => initial ++ values.toArray) := by
  induction xs generalizing initial with
  | nil => simp only [List.forIn_nil,List.mapM_nil]; rfl
  | cons x xs ih =>
    rw [List.forIn_cons,List.mapM_cons]
    cases hx : f x with
    | error e => rfl
    | ok value =>
      simp only [ok_bind]
      change (forIn xs (initial.push value) fun x acc => do
        let value ← f x
        pure (.yield (acc.push value))) = _
      rw [ih]
      cases tail : xs.mapM f with
      | error e => rfl
      | ok values =>
        simp only [ok_bind,Except.map]
        change Except.ok (initial.push value ++ values.toArray) =
          Except.ok (initial ++ (value::values).toArray)
        congr 1
        apply Array.toList_inj.mp
        simp

def tableHead (n : Names) (o : Offsets) (b : Nat) : Nat :=
  n.table+o.buckets+b*o.headSize+o.first

def decodeBucket (n : Names) (o : Offsets) (m : DataMem) (b : Nat) : Decode (List IndexEntry) := do
  let first ← word m s!"bucket[{b}].head" (tableHead n o b) 8
  bucket n o m b (n.owners.length+1) first (tableHead n o b) []

def decodeOwners (n : Names) (o : Offsets) (m : DataMem) : Decode (List (IndexOwner × Option PeerId)) :=
  n.owners.mapM fun (owner,a) => do
    let path := s!"owner[{repr owner}].peer"
    let ptr ← word m path (a+o.peer) 8
    return (owner, ← peerId n path ptr)

def decodeCounts (n : Names) (o : Offsets) (m : DataMem) : Decode (List (PeerId × Nat)) :=
  n.peers.mapM fun (id,a) => do
    return (id, ← word m s!"peer[{id}].refcount" (a+o.peerRefcount) 4)

/-- A proved normal form of the unchanged runtime decoder, exposing its
independent components without installing a second state relation. -/
theorem reconstruct_normal (n : Names) (o : Offsets) (m : DataMem) :
    reconstruct n o m = (do
      n.validate o
      let buckets ← (List.range 8192).mapM (decodeBucket n o m)
      let ownerWords ← decodeOwners n o m
      let refcounts ← decodeCounts n o m
      return {buckets := buckets.toArray,ownerWords,refcounts}) := by
  unfold reconstruct
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    show ([:8192] : Std.Legacy.Range).size = 8192 from rfl,
    ←List.range_eq_range']
  have collected := collect_eq_mapM (decodeBucket n o m) (List.range 8192) #[]
  simp only [Array.empty_append] at collected
  simp only [decodeBucket,tableHead,bind_assoc] at collected
  rw [collected]
  cases n.validate o <;> cases (List.range 8192).mapM (decodeBucket n o m) <;> rfl

theorem reconstruct_components {n o m state}
    (related : reconstruct n o m=.ok state) :
    n.validate o=.ok () ∧
    (List.range 8192).mapM (decodeBucket n o m)=.ok state.buckets.toList ∧
    decodeOwners n o m=.ok state.ownerWords ∧ decodeCounts n o m=.ok state.refcounts := by
  rw [reconstruct_normal] at related
  obtain ⟨checked,validation,related⟩ := bind_ok related
  cases checked
  obtain ⟨buckets,bucketsRead,related⟩ := bind_ok related
  obtain ⟨owners,ownersRead,related⟩ := bind_ok related
  obtain ⟨counts,countsRead,related⟩ := bind_ok related
  have equal : ({buckets := buckets.toArray,ownerWords := owners,refcounts := counts} : LookupState)=state := Except.ok.inj related
  subst state
  exact ⟨validation,by simpa using bucketsRead,ownersRead,countsRead⟩

#print axioms reconstruct_normal
#print axioms reconstruct_components

theorem reconstruct_of_components {n o m state}
    (validation : n.validate o=.ok ())
    (buckets : (List.range 8192).mapM (decodeBucket n o m)=.ok state.buckets.toList)
    (owners : decodeOwners n o m=.ok state.ownerWords)
    (counts : decodeCounts n o m=.ok state.refcounts) : reconstruct n o m=.ok state := by
  rw [reconstruct_normal,validation,buckets,owners,counts]
  cases state
  rfl

/-- Lift local bucket effects while framing all owner words and counts. -/
theorem reconstruct_map_buckets (n : Names) (o : Offsets) (before after : DataMem)
    (f : List IndexEntry → List IndexEntry)
    (buckets : ∀ b < 8192, decodeBucket n o after b = (decodeBucket n o before b).map f)
    (owners : decodeOwners n o after=decodeOwners n o before)
    (counts : decodeCounts n o after=decodeCounts n o before) :
    reconstruct n o after = (reconstruct n o before).map
      (fun state => {state with buckets := state.buckets.map f}) := by
  have changed : (List.range 8192).mapM (decodeBucket n o after) =
      ((List.range 8192).mapM (decodeBucket n o before)).map (List.map f) := by
    rw [←Trie.mapM_map_result]
    apply Trie.mapM_same
    intro b member
    exact buckets b (List.mem_range.mp member)
  rw [reconstruct_normal,reconstruct_normal,changed,owners,counts]
  cases n.validate o with
  | error e => rfl
  | ok checked =>
    cases (List.range 8192).mapM (decodeBucket n o before) with
    | error e => rfl
    | ok values =>
      cases decodeOwners n o before <;> cases decodeCounts n o before <;> try rfl
      rename_i ownerValues countValues
      change Except.ok ({buckets := (values.map f).toArray, ownerWords := ownerValues, refcounts := countValues} : LookupState) =
        Except.ok {buckets := values.toArray.map f, ownerWords := ownerValues, refcounts := countValues}
      rw [List.map_toArray]

theorem target_remove (d : Device) (removed : IndexOwner) :
    target {d with indexTable := d.indexTable.filter (fun e => !(e.owner==removed))} =
      { (target d) with buckets := (target d).buckets.map (List.filter (fun e => !(e.owner==removed))) } := by
  unfold target
  dsimp only [Id.run,Bind.bind,Pure.pure]
  simp only [Array.map_map]
  congr 1
  apply Array.map_congr_left
  intro b _
  simp only [Function.comp_apply,List.filter_filter,Bool.and_comm]

theorem reconstruct_remove {n o before after d removed}
    (related : Corresponds n o before d)
    (buckets : ∀ b < 8192, decodeBucket n o after b =
      (decodeBucket n o before b).map (List.filter (fun e => !(e.owner==removed))))
    (owners : decodeOwners n o after=decodeOwners n o before)
    (counts : decodeCounts n o after=decodeCounts n o before) :
    Corresponds n o after {d with indexTable := d.indexTable.filter (fun e => !(e.owner==removed))} := by
  unfold Corresponds
  rw [reconstruct_map_buckets n o before after _ buckets owners counts,related]
  exact congrArg Except.ok (target_remove d removed).symm

#print axioms reconstruct_remove
end Binary.Pair.Index
