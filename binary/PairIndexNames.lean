import PairBucketEdges
import PairAllocationProof

namespace Binary.Pair.Index
open Leanux Leanux.WG
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

structure Layout (o : Offsets) : Prop where
  tableSize : o.tableSize=8192*8
  headSize : o.headSize=8
  first : o.first=0
  buckets : o.buckets=0
  entrySize : o.entrySize=32
  peer : o.peer=0
  hash : o.hash=8
  next : o.next=0
  pprev : o.pprev=8
  kind : o.kind=24
  index : o.index=28
  peerRefcount : o.peerRefcount=Layouts.peer_refcount
  keypairEntry : o.keypairEntry=0

theorem validate_basic {n : Names} {o : Offsets} (checked : n.validate o=.ok ()) :
    Layout o ∧ (n.owners.map Prod.fst).Nodup ∧ (n.owners.map Prod.snd).Nodup ∧
      (n.peers.map Prod.fst).Nodup ∧ (n.peers.map Prod.snd).Nodup := by
  unfold Names.validate at checked
  obtain ⟨table,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨fields,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨peers,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨owners,_⟩ := check_ok _ _ _ _ checked
  have tb : o.tableSize=8192*o.headSize ∧ o.headSize=8 ∧ o.first=0 ∧ o.buckets=0 ∧ o.entrySize=32 := by
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using table
  have fs : o.peer=0 ∧ o.hash=8 ∧ o.next=0 ∧ o.pprev=8 ∧ o.kind=24 ∧ o.index=28 ∧
      o.peerRefcount=Layouts.peer_refcount ∧ o.keypairEntry=0 ∧
      o.peerHandshake+o.handshakeEntry+o.entrySize≤Layouts.peerSize := by
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc,decide_eq_true_eq,
      Layouts.entry_peer,Layouts.entry_index_hash,Layouts.node_next,Layouts.node_pprev,
      Layouts.entry_type,Layouts.entry_index,Layouts.keypair_entry] using fields
  have po : (n.peers.map Prod.fst).eraseDups.length=n.peers.length ∧
      (n.peers.map Prod.snd).eraseDups.length=n.peers.length := by simpa using peers
  have ow : (n.owners.map Prod.fst).eraseDups.length=n.owners.length ∧
      (n.owners.map Prod.snd).eraseDups.length=n.owners.length := by simpa using owners
  refine ⟨⟨by rw [tb.1,tb.2.1],tb.2.1,tb.2.2.1,tb.2.2.2.1,tb.2.2.2.2,
    fs.1,fs.2.1,fs.2.2.1,fs.2.2.2.1,fs.2.2.2.2.1,fs.2.2.2.2.2.1,
    fs.2.2.2.2.2.2.1,fs.2.2.2.2.2.2.2.1⟩,?_,?_,?_,?_⟩
  · apply nodup_of_eraseDups_length; simpa using ow.1
  · apply nodup_of_eraseDups_length; simpa using ow.2
  · apply nodup_of_eraseDups_length; simpa using po.1
  · apply nodup_of_eraseDups_length; simpa using po.2

theorem ownerAt_named {n : Names} {path : String} {base : Nat} {owner : IndexOwner}
    (read : ownerAt n path base=.ok owner) : (owner,base) ∈ n.owners := by
  unfold ownerAt at read
  cases found : n.owners.find? (·.2==base) with
  | none => rw [found] at read; cases read
  | some pair =>
    rw [found] at read
    have id : pair.1=owner := Except.ok.inj read
    have address : pair.2=base := by simpa using List.find?_some found
    simpa only [←id,←address] using List.mem_of_find?_eq_some found

theorem NodeFields.named {n o m b link previous next entry}
    (fields : NodeFields n o m b link previous next entry) :
    (entry.owner,link-o.hash) ∈ n.owners := ownerAt_named fields.owner

theorem unique_first {α β : Type} {pairs : List (α×β)}
    (unique : (pairs.map Prod.fst).Nodup) {id : α} {a b : β}
    (left : (id,a) ∈ pairs) (right : (id,b) ∈ pairs) : a=b := by
  induction pairs with
  | nil => cases left
  | cons pair rest ih =>
    have nd := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with equal | leftTail
    · subst pair
      rcases List.mem_cons.mp right with equal | rightTail
      · exact congrArg Prod.snd equal.symm
      · exact False.elim (nd.1 (List.mem_map.mpr ⟨(id,b),rightTail,rfl⟩))
    · rcases List.mem_cons.mp right with equal | rightTail
      · subst pair
        exact False.elim (nd.1 (List.mem_map.mpr ⟨(id,a),leftTail,rfl⟩))
      · exact ih nd.2 leftTail rightTail

theorem NodeFields.owner_iff {n o m b b' link prev next entry other otherPrev otherNext otherEntry}
    (left : NodeFields n o m b link prev next entry)
    (right : NodeFields n o m b' other otherPrev otherNext otherEntry)
    (unique : (n.owners.map Prod.fst).Nodup) : entry.owner=otherEntry.owner ↔ link=other := by
  constructor
  · intro same
    have named := right.named
    rw [←same] at named
    have bases := unique_first unique left.named named
    have := left.valid
    have := right.valid
    omega
  · intro same
    subst other
    have lh := left.owner
    have rh := right.owner
    unfold ownerAt at lh rh
    cases found : n.owners.find? (·.2==link-o.hash) with
    | none => rw [found] at lh; cases lh
    | some pair =>
      simp only [found] at lh rh
      exact (Except.ok.inj lh).symm.trans (Except.ok.inj rh)

#print axioms validate_basic
#print axioms NodeFields.owner_iff
end Binary.Pair.Index
