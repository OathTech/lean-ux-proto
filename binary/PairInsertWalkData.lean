import PairInsertRetryState

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- The containing-object base is non-NULL by the existing executable names
validation, not an extra restriction on the insertion entry domain. -/
theorem validate_owner_range {n o owner base} (checked : Names.validate n o=.ok ())
    (named : (owner,base) ∈ n.owners) : 0<base ∧ base+o.entrySize<2^64 := by
  unfold Names.validate at checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,owners,_⟩ := bind_ok checked
  have each := forIn_ok (P := fun pair : IndexOwner×Nat => 0<pair.2 ∧ pair.2+o.entrySize<2^64)
    (fun pair _ before after run => by
      rcases pair with ⟨id,address⟩
      obtain ⟨range,rest⟩ := check_ok _ _ _ _ run
      refine ⟨(),?_,by simpa only [Bool.and_eq_true,decide_eq_true_eq] using range⟩
      cases id with
      | keypair id => exact (Except.ok.inj rest).symm
      | handshake id =>
        dsimp only at rest
        cases found : n.peers.find? (·.1==id) with
        | none => rw [found] at rest; cases rest
        | some peer =>
          rcases peer with ⟨pid,peer⟩
          rw [found] at rest
          obtain ⟨_,rest⟩ := check_ok _ _ _ _ rest
          exact (Except.ok.inj rest).symm) owners
  exact each (owner,base) named

theorem NodeFields.base_positive {n o m b link previous next entry}
    (fields : NodeFields n o m b link previous next entry) (checked : n.validate o=.ok ()) :
    0<link-o.hash := (validate_owner_range checked fields.named).1

theorem NodeFields.base_nonzero {n o m b link previous next entry}
    (fields : NodeFields n o m b link previous next entry) (checked : n.validate o=.ok ()) :
    BitVec.ofNat 64 (link-o.hash)≠0 := by
  have range := validate_owner_range checked fields.named
  intro equal
  have values := congrArg BitVec.toNat equal
  change (link-o.hash)%2^64=0 at values
  rw [Nat.mod_eq_of_lt (by omega : link-o.hash<2^64)] at values
  omega

theorem NodeFields.index_load {n o m b link previous next entry}
    (fields : NodeFields n o m b link previous next entry) (layout : Layout o) :
    m.loadInt (BitVec.ofNat 64 (link-o.hash)+28) 4=some entry.index := by
  have read := word_loadInt _ _ _ _ _ fields.index
  rw [layout.index,BitVec.ofNat_add] at read
  exact read

theorem NodeFields.link_nonzero {n o m b link previous next entry}
    (fields : NodeFields n o m b link previous next entry) (checked : n.validate o=.ok ()) :
    BitVec.ofNat 64 link≠0 := by
  have range := validate_owner_range checked fields.named
  have layout := (validate_basic checked).1
  have valid := fields.valid
  rw [layout.hash,layout.entrySize] at range
  rw [layout.hash] at valid
  have bound : link<2^64 := by omega
  intro equal
  have values := congrArg BitVec.toNat equal
  change link%2^64=0 at values
  rw [Nat.mod_eq_of_lt bound] at values
  exact fields.nonzero values

theorem NodeFields.next_load {n o m b link previous next entry}
    (fields : NodeFields n o m b link previous next entry) (layout : Layout o) :
    m.loadInt (BitVec.ofNat 64 (link-o.hash)+8) 8=some next := by
  have read := word_loadInt _ _ _ _ _ fields.forward
  have valid := fields.valid
  rw [layout.hash] at valid
  rw [layout.next,Nat.add_zero] at read
  change m.loadInt (BitVec.ofNat 64 (link-o.hash)+BitVec.ofNat 64 8) 8=some (next : Int)
  rw [←BitVec.ofNat_add,layout.hash,show link-8+8=link by omega]
  exact read

#print axioms validate_owner_range
#print axioms NodeFields.base_nonzero
end Binary.Pair.Index
