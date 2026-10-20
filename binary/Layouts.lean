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
def deviceSize : Nat := 592
def device_cookie_checker : Nat := 304
def device_peer_hashtable : Nat := 448
def device_peer_list : Nat := 552
def cookieSize : Nat := 144
def cookie_secret : Nat := 0
def cookie_secret_birthdate : Nat := 96
def pubkeyTableSize : Nat := 16424
def pubkeyTable_key : Nat := 16384
def indexTableSize : Nat := 65536
def indexTable_hashtable : Nat := 0
def device_index_hashtable : Nat := 456
def peer_endpoint : Nat := 160
def endpointSize : Nat := 44
def endpoint_addr : Nat := 0
def endpoint_addr4 : Nat := 0
def endpoint_addr6 : Nat := 0
def endpoint_src4 : Nat := 28
def endpoint_src_if4 : Nat := 32
def endpoint_src6 : Nat := 28
def sockaddrSize : Nat := 16
def sockaddr_sa_family : Nat := 0
def sockaddr4Size : Nat := 16
def sockaddr4_sin_family : Nat := 0
def sockaddr4_sin_port : Nat := 2
def sockaddr4_sin_addr : Nat := 4
def sockaddr6Size : Nat := 28
def sockaddr6_sin6_family : Nat := 0
def sockaddr6_sin6_port : Nat := 2
def sockaddr6_sin6_flowinfo : Nat := 4
def sockaddr6_sin6_addr : Nat := 8
def sockaddr6_sin6_scope_id : Nat := 24
def ratelimiterKeyAddress : BitVec 64 := .ofNat 64 18446744071595474592
def peerSize : Nat := 1520
def peer_refcount : Nat := 1056
def peer_serial_work_cpu : Nat := 128
def peer_keypairs : Nat := 136
def list_next : Nat := 0
def list_prev : Nat := 8
def peer_peer_list : Nat := 1080
def peer_allowedips_list : Nat := 1096
def allowedipsNode_peer_list : Nat := 56
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
/-- Key bytes, timestamp bit pattern and validity byte; no key placeholder is used here. -/
def SymmetricFields (m : Mem 64) (a : BitVec 64) (k : Leanux.WG.SymmetricKey) : Prop :=
  m.loadBytes (a + .ofNat 64 symmetric_key) 32 = some k.key ∧
  m.loadInt (a + .ofNat 64 symmetric_birthdate) 8 = some k.birthdate.toBitVec.toNat ∧
  m.loadInt (a + .ofNat 64 symmetric_is_valid) 1 = some (if k.isValid then 1 else 0)
/-- All non-pointer mirror keypair fields. The entry peer word is
    explicit: the owning-object and index-table views must agree on it. -/
def KeypairFields (m : Mem 64) (a peerWord : BitVec 64) (k : Leanux.WG.Keypair) : Prop :=
  KeypairSnapshotFields m a k ∧
  SymmetricFields m (a + .ofNat 64 keypair_sending) k.sending ∧
  SymmetricFields m (a + .ofNat 64 keypair_receiving) k.receiving ∧
  m.loadInt (a + .ofNat 64 keypair_sending_counter) 8 = some (k.sendingCounter : Int) ∧
  m.loadInt (a + .ofNat 64 keypair_remote_index) 4 = some (k.remoteIndex : Int) ∧
  m.loadInt (a + .ofNat 64 keypair_i_am_the_initiator) 1 = some (if k.iAmTheInitiator then 1 else 0) ∧
  m.loadInt (a + .ofNat 64 keypair_refcount) 4 = some (k.refcount : Int) ∧
  m.loadInt (a + .ofNat 64 (keypair_entry + entry_peer)) 8 = some peerWord.toNat
end Binary.Layouts
