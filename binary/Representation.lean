import Layouts
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

#print axioms bucket_tail

end Binary
