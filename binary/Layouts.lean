import Kraken.Mem
namespace Binary.Layouts
-- Generated DWARF offsets; physical pointer interpretation is separate.
def entrySize : Nat := 32
def headSize : Nat := 8
def entry_peer : Nat := 0
def entry_index_hash : Nat := 8
def entry_type : Nat := 24
def entry_index : Nat := 28
def node_next : Nat := 0
def node_pprev : Nat := 8
/-- The three C scalar fields, represented by exact word equality. -/
def EntryFields (m : Mem 64) (a peer : BitVec 64) (kind index : BitVec 32) : Prop :=
  m.loadInt (a + .ofNat 64 entry_peer) 8 = some peer.toNat ∧
  m.loadInt (a + .ofNat 64 entry_type) 4 = some kind.toNat ∧
  m.loadInt (a + .ofNat 64 entry_index) 4 = some index.toNat
end Binary.Layouts
