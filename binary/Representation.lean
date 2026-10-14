import Layouts
import Memory
import Leanux.WG.Types

namespace Binary

abbrev Address := BitVec 64

def kindWord : Leanux.WG.IndexKind → BitVec 32
  | .handshake => 1
  | .keypair => 2

/-- Ordered intrusive chain. The head and next fields point to the embedded
    hlist_node, not to the beginning of index_hashtable_entry. Every recursive
    call consumes one list entry, so cycles cannot represent a finite bucket.
    This is a local heap predicate, not the whole-world adequacy relation. -/
def Bucket (peers : Leanux.WG.PeerId → Address) (m : Mem 64) :
    Address → List (Address × Leanux.WG.IndexEntry) → Prop
  | head, [] => head = 0
  | head, (a, e) :: rest =>
      a ≠ 0 ∧ head ≠ 0 ∧ head = a + .ofNat 64 Layouts.entry_index_hash ∧
      e.index < 2^32 ∧ peers e.peer ≠ 0 ∧
      Layouts.EntryFields m a (peers e.peer) (kindWord e.kind) (.ofNat 32 e.index) ∧
      ∃ next, m.loadInt (head + .ofNat 64 Layouts.node_next) 8 = some next.toNat ∧
        Bucket peers m next rest

theorem bucket_empty (peers : Leanux.WG.PeerId → Address) (m : Mem 64) (head : Address) :
    Bucket peers m head [] ↔ head = 0 := Iff.rfl

theorem bucket_cons_nonnull (peers : Leanux.WG.PeerId → Address) (m : Mem 64)
    (head a : Address) (e : Leanux.WG.IndexEntry) (rest)
    (h : Bucket peers m head ((a, e) :: rest)) : head ≠ 0 := h.2.1

theorem bucket_tail (peers : Leanux.WG.PeerId → Address) (m : Mem 64)
    (head a : Address) (e : Leanux.WG.IndexEntry) (rest)
    (h : Bucket peers m head ((a, e) :: rest)) :
    ∃ next, m.loadInt (head + .ofNat 64 Layouts.node_next) 8 = some next.toNat ∧
      Bucket peers m next rest := h.2.2.2.2.2.2

/-- A disjoint write preserves every exact field in the represented chain.
    The premise refers to physical entry bytes, not to a ghost copy of entries. -/
theorem Bucket.frame (peers : Leanux.WG.PeerId → Address)
    {before after : Mem 64} {writes : Address → Prop}
    (same : EqualOutside writes before after) (es : List (Address × Leanux.WG.IndexEntry))
    (disjoint : ∀ cell ∈ es, ∀ i < Layouts.entrySize, ¬ writes (cell.1 + .ofNat 64 i))
    (head : Address) (represented : Bucket peers before head es) :
    Bucket peers after head es := by
  induction es generalizing head with
  | nil => exact represented
  | cons cell es ih =>
    rcases cell with ⟨a, e⟩
    rcases represented with ⟨ha, hh, hnode, hi, hp, fields, next, hn, tail⟩
    have unchanged (off n : Nat) (bound : off + n ≤ Layouts.entrySize) :
        before.loadInt (a + .ofNat 64 off) n = after.loadInt (a + .ofNat 64 off) n := by
      apply same.loadInt
      intro i hi
      have h := disjoint (a, e) (by simp) (off + i) (by omega)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
    refine ⟨ha, hh, hnode, hi, hp, ?_, next, ?_, ?_⟩
    · rcases fields with ⟨peer, kind, index⟩
      exact ⟨(unchanged Layouts.entry_peer 8 (by decide)).symm.trans peer,
        (unchanged Layouts.entry_type 4 (by decide)).symm.trans kind,
        (unchanged Layouts.entry_index 4 (by decide)).symm.trans index⟩
    · rw [hnode] at hn ⊢
      simp only [Layouts.entry_index_hash, Layouts.node_next, BitVec.add_zero] at hn ⊢
      exact (unchanged 8 8 (by decide)).symm.trans hn
    · exact ih (fun cell hc => disjoint cell (by simp [hc])) next tail

#print axioms Bucket.frame

#print axioms bucket_tail

end Binary
