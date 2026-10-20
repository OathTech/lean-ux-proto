import PairExcept

namespace Binary.Pair

/-- Diagnostic paths affect only decoding errors, not a successful value. -/
theorem word_path {m : DataMem} {path : String} {base size value : Nat}
    (read : word m path base size=.ok value) (other : String) :
    word m other base size=.ok value := by
  unfold word at read ⊢
  split at read
  · rename_i bounded
    rw [ite_eq_left bounded]
    cases loaded : m.loadBytes (.ofNat 64 base) size <;> simp_all
  · cases read

theorem word_values {m : DataMem} {path other : String} {base size value result : Nat}
    (left : word m path base size=.ok value)
    (right : word m other base size=.ok result) : value=result :=
  Except.ok.inj ((word_path left other).symm.trans right)

end Binary.Pair

namespace Binary.Pair.Index
open Leanux Leanux.WG

abbrev Nodes := List (Nat × IndexEntry)

def head (nodes : Nodes) : Nat := nodes.head?.map Prod.fst |>.getD 0

def ownerKind : IndexOwner → Nat
  | .handshake _ => 1
  | .keypair _ => 2

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f) = f value := rfl

/-- A finite presentation extracted from the executable decoder. The stored
word equations are its conclusions, never an independent entry assumption. -/
structure NodeFields (n : Names) (o : Offsets) (m : DataMem) (b : Nat)
    (link previous next : Nat) (entry : IndexEntry) : Prop where
  nonzero : link ≠ 0
  valid : o.hash ≤ link
  owner : ownerAt n s!"bucket[{b}].owner" (link-o.hash) = .ok entry.owner
  index : word m s!"bucket[{b}].index" (link-o.hash+o.index) 4 = .ok entry.index
  bucket : entry.index % 8192 = b
  kind : word m s!"bucket[{b}].kind" (link-o.hash+o.kind) 4 =
    .ok (ownerKind entry.owner)
  back : word m s!"bucket[{b}].pprev" (link+o.pprev) 8 = .ok previous
  forward : word m s!"bucket[{b}].next" (link+o.next) 8 = .ok next

inductive Chain (n : Names) (o : Offsets) (m : DataMem) (b : Nat) : Nat → Nodes → Prop
  | nil (previous : Nat) : Chain n o m b previous []
  | cons {previous link entry rest}
      (fields : NodeFields n o m b link previous (head rest) entry)
      (tail : Chain n o m b (link+o.next) rest) :
      Chain n o m b previous ((link,entry)::rest)

theorem bucket_zero (n : Names) (o : Offsets) (m : DataMem) (b fuel previous : Nat)
    (seen : List Nat) : bucket n o m b fuel 0 previous seen = .ok [] := by
  cases fuel <;> rfl

/-- Successful decoding supplies shape, fuel sufficiency and the exact
no-cycle facts needed for a later structural edit. -/
theorem bucket_shape {n o m b fuel link previous seen entries}
    (ok : bucket n o m b fuel link previous seen = .ok entries) :
    ∃ nodes : Nodes, entries=nodes.map Prod.snd ∧ link=head nodes ∧
      Chain n o m b previous nodes ∧ nodes.length≤fuel ∧
      (nodes.map Prod.fst).Nodup ∧ ∀ p ∈ nodes.map Prod.fst, p ∉ seen := by
  induction fuel generalizing link previous seen entries with
  | zero =>
    by_cases zero : link=0
    · subst link
      have empty : entries=[] := Except.ok.inj ok |>.symm
      subst entries
      exact ⟨[],rfl,rfl,.nil _,Nat.le_refl _,by simp,by simp⟩
    · simp [bucket,zero] at ok
  | succ fuel ih =>
    by_cases zero : link=0
    · subst link
      rw [bucket_zero] at ok
      have empty : entries=[] := Except.ok.inj ok |>.symm
      subst entries
      exact ⟨[],rfl,rfl,.nil _,Nat.zero_le _,by simp,by simp⟩
    · rw [bucket] at ok
      simp only [show (link==0)=false from beq_eq_false_iff_ne.mpr zero,
        Bool.false_eq_true,↓reduceIte] at ok
      by_cases valid : o.hash≤link
      · simp only [valid,↓reduceIte] at ok
        by_cases cycle : seen.contains link=true
        · simp only [cycle] at ok; cases ok
        · simp only [cycle] at ok
          obtain ⟨owner,ownerRead,ok⟩ := bind_ok ok
          obtain ⟨index,indexRead,ok⟩ := bind_ok ok
          obtain ⟨bucketAt,ok⟩ := check_ok _ _ _ _ ok
          obtain ⟨kind,kindRead,ok⟩ := bind_ok ok
          obtain ⟨kindAt,ok⟩ := check_ok _ _ _ _ ok
          obtain ⟨back,backRead,ok⟩ := bind_ok ok
          obtain ⟨backAt,ok⟩ := check_ok _ _ _ _ ok
          obtain ⟨next,nextRead,ok⟩ := bind_ok ok
          obtain ⟨rest,restRead,ok⟩ := bind_ok ok
          have result : ({index,owner} : IndexEntry)::rest=entries := Except.ok.inj ok
          obtain ⟨nodes,equal,atHead,shape,length,distinct,fresh⟩ := ih restRead
          have bk : back=previous := by simpa using backAt
          have kd : kind=ownerKind owner := by
            cases owner <;> simpa only [ownerKind,beq_iff_eq] using kindAt
          refine ⟨(link,⟨index,owner⟩)::nodes,?_,rfl,
            .cons ⟨zero,valid,ownerRead,indexRead,by simpa using bucketAt,?_,?_,?_⟩ shape,
            by simpa using Nat.succ_le_succ length,?_,?_⟩
          · rw [←result,equal]; rfl
          · simpa only [kd] using kindRead
          · simpa only [bk] using backRead
          · simpa only [atHead] using nextRead
          · simp only [List.map_cons,List.nodup_cons]
            exact ⟨fun present => fresh link present (by simp),distinct⟩
          · intro p member
            rcases List.mem_cons.mp member with rfl | member
            · simpa using cycle
            · exact fun old => fresh p member (by simp [old])
      · simp only [valid,↓reduceIte] at ok; cases ok

/-- The finite presentation is sufficient for the actual executable decoder.
Changing the presentation in a proof does not replace the runtime relation. -/
theorem Chain.decode {n o m b previous nodes}
    (shape : Chain n o m b previous nodes) (fuel : Nat) (seen : List Nat)
    (length : nodes.length≤fuel) (distinct : (nodes.map Prod.fst).Nodup)
    (fresh : ∀ p ∈ nodes.map Prod.fst, p ∉ seen) :
    bucket n o m b fuel (head nodes) previous seen = .ok (nodes.map Prod.snd) := by
  induction shape generalizing fuel seen with
  | nil previous => exact bucket_zero n o m b fuel previous seen
  | @cons previous link entry rest fields tail ih =>
    cases fuel with
    | zero => simp at length
    | succ fuel =>
      have cycle : link ∉ seen := fresh link (by simp)
      have nd := List.nodup_cons.mp distinct
      have recurse := ih fuel (link::seen) (by simpa using length)
        nd.2 (by
          intro p member present
          rcases List.mem_cons.mp present with rfl | old
          · exact nd.1 member
          · exact fresh p (by simp [member]) old)
      change bucket n o m b (fuel+1) link previous seen = .ok (entry::rest.map Prod.snd)
      rw [bucket]
      simp only [show (link==0)=false from beq_eq_false_iff_ne.mpr fields.nonzero,
        Bool.false_eq_true,↓reduceIte,fields.valid,
        show seen.contains link=false from by simpa using cycle,
        fields.owner,fields.index,fields.bucket,fields.kind,fields.back,
        fields.forward,ok_bind,ownerKind,beq_self_eq_true,recurse]
      cases entry with
      | mk index owner => cases owner <;> rfl

#print axioms bucket_shape
#print axioms Chain.decode
end Binary.Pair.Index
