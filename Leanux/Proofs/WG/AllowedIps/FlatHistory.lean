import Leanux.Proofs.WG.AllowedIps.Insertion

/-! Independent flat-prefix semantics: bindings contain canonical prefix bits
and raw owner labels, with no trie or node identifiers. Membership, rather than
the implementation's traversal order, relates the two representations. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux
set_option maxHeartbeats 1000000

abbrev FlatBinding := (Nat × Nat) × Nat
abbrev FlatTable := List FlatBinding

def canonical (width : Nat) (e : Entry) : FlatBinding := (e.prefixKey width, e.peer)

def flatInsert (width addr cidr pid : Nat) (xs : FlatTable) : FlatTable :=
  ((cidr, prefixBits width cidr addr), pid) ::
    xs.filter (fun b => b.1 != (cidr, prefixBits width cidr addr))

def flatRemove (pid : Nat) (xs : FlatTable) : FlatTable := xs.filter (fun b => b.2 != pid)

def FlatAgree (width : Nat) (t : Tree) (xs : FlatTable) : Prop :=
  ∀ b, b ∈ t.bindings width ↔ b ∈ xs

theorem flatAgree_empty (width : Nat) : FlatAgree width .empty [] := by
  intro b
  rfl

theorem insertFresh_canonical (t : Tree) (width fresh addr cidr pid : Nat) :
    canonical width (t.insertFresh width fresh addr cidr pid).binding =
      ((cidr, prefixBits width cidr addr), pid) := by
  simp only [canonical, Tree.insertFresh_prefixKey, Tree.insertFresh_peer]

theorem FlatAgree.insert (he : FlatAgree width t xs) (hv : t.Valid width)
    (ha : addr < 2 ^ width) (hc : cidr ≤ width) (fresh pid : Nat) :
    FlatAgree width (t.insertFresh width fresh addr cidr pid).tree (flatInsert width addr cidr pid xs) := by
  intro b
  simp only [Tree.bindings, List.mem_map, flatInsert, List.mem_cons, List.mem_filter, bne_iff_ne]
  constructor
  · rintro ⟨e, hm, rfl⟩
    rcases (Tree.insertFresh_entries hv ha hc fresh pid e).mp hm with rfl | ⟨hm, hn⟩
    · exact .inl (insertFresh_canonical t width fresh addr cidr pid)
    · exact .inr ⟨(he _).mp (List.mem_map.mpr ⟨e, hm, rfl⟩), hn⟩
  · rintro (rfl | ⟨hm, hn⟩)
    · exact ⟨_, (Tree.insertFresh_entries hv ha hc fresh pid _).mpr (.inl rfl),
        insertFresh_canonical t width fresh addr cidr pid⟩
    · obtain ⟨e, hentry, rfl⟩ := List.mem_map.mp ((he _).mpr hm)
      exact ⟨e, (Tree.insertFresh_entries hv ha hc fresh pid e).mpr (.inr ⟨hentry, hn⟩), rfl⟩

theorem FlatAgree.remove (he : FlatAgree width t xs)
    (hentries : u.entries = t.entries.filter (fun e => e.peer != pid)) :
    FlatAgree width u (flatRemove pid xs) := by
  intro b
  simp only [Tree.bindings, hentries, List.mem_map, List.mem_filter, bne_iff_ne,
    flatRemove]
  constructor
  · rintro ⟨e, ⟨hm, hn⟩, rfl⟩
    exact ⟨(he _).mp (List.mem_map.mpr ⟨e, hm, rfl⟩), hn⟩
  · rintro ⟨hm, hn⟩
    obtain ⟨e, hentry, rfl⟩ := List.mem_map.mp ((he _).mpr hm)
    exact ⟨e, ⟨hentry, hn⟩, rfl⟩

def FlatMatches (width key : Nat) (b : FlatBinding) : Prop :=
  b.1.2 = prefixBits width b.1.1 key

def FlatWinner (width key : Nat) (xs : FlatTable) : Option FlatBinding → Prop
  | none => ∀ b ∈ xs, ¬ FlatMatches width key b
  | some b => b ∈ xs ∧ FlatMatches width key b ∧
      ∀ other ∈ xs, FlatMatches width key other → other.1.1 ≤ b.1.1

theorem FlatAgree.winner (he : FlatAgree width t xs)
    (hw : Winner width key t.entries answer) :
    FlatWinner width key xs (answer.map (canonical width)) := by
  cases answer with
  | none =>
    intro b hb hm
    obtain ⟨e, hmemb, rfl⟩ := List.mem_map.mp ((he b).mpr hb)
    exact hw e hmemb hm
  | some e =>
    refine ⟨(he _).mp (List.mem_map.mpr ⟨e, hw.1, rfl⟩), hw.2.1, ?_⟩
    intro b hb hm
    obtain ⟨other, hmemb, rfl⟩ := List.mem_map.mp ((he b).mpr hb)
    exact hw.2.2 other hmemb hm

end Leanux.Proofs.WG.AllowedIps
