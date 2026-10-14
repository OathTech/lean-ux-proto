import Kraken.Mem
import Leanux.WG.Types
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
def keypairSize : Nat := 1208
def keypair_entry : Nat := 0
def keypair_sending : Nat := 32
def keypair_sending_counter : Nat := 80
def keypair_receiving : Nat := 88
def keypair_receiving_counter : Nat := 136
def keypair_remote_index : Nat := 1168
def keypair_i_am_the_initiator : Nat := 1172
def keypair_refcount : Nat := 1176
def keypair_rcu : Nat := 1184
def keypair_internal_id : Nat := 1200
def replaySize : Nat := 1032
def replay_counter : Nat := 0
def replay_lock : Nat := 8
def replay_backtrack : Nat := 8
def slotsSize : Nat := 24
def slots_current_keypair : Nat := 0
def slots_previous_keypair : Nat := 8
def slots_next_keypair : Nat := 16
def slots_keypair_update_lock : Nat := 24
def symmetricSize : Nat := 48
def symmetric_key : Nat := 0
def symmetric_birthdate : Nat := 32
def symmetric_is_valid : Nat := 40
def peerSize : Nat := 1520
def peer_refcount : Nat := 1056
def peer_keypairs : Nat := 136
def keypairCounterAddress : BitVec 64 := .ofNat 64 18446744071595474496
def replayWords : Nat := 128
def replayWordBytes : Nat := 8
/-- Exact physical replay counter and all 128 bitmap words. -/
def ReplayFields (m : Mem 64) (a : BitVec 64) (r : Leanux.WG.ReplayCounter) : Prop :=
  m.loadInt (a + .ofNat 64 replay_counter) 8 = some (r.counter : Int) ∧
  r.backtrack.size = replayWords ∧
  ∀ i (hi : i < r.backtrack.size),
    m.loadInt (a + .ofNat 64 (replay_backtrack + i * replayWordBytes)) replayWordBytes = some (r.backtrack[i] : Int)
/-- The fields read by the keypair-lifetime snapshot. Pointer/store
    membership and the remaining keypair fields are separate obligations. -/
def KeypairSnapshotFields (m : Mem 64) (a : BitVec 64) (k : Leanux.WG.Keypair) : Prop :=
  m.loadInt (a + .ofNat 64 keypair_internal_id) 8 = some (k.internalId : Int) ∧
  ReplayFields m (a + .ofNat 64 keypair_receiving_counter) k.receivingCounter
def KeypairCounterField (m : Mem 64) (counter : Nat) : Prop :=
  m.loadInt keypairCounterAddress 8 = some (counter : Int)
end Binary.Layouts
