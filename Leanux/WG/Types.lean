import Leanux.WG.Curve25519
import Std.Data.TreeMap

/-!
# WireGuard state (drivers/net/wireguard)

Shaped like the C structures of the configuration path: `struct wg_device`,
`struct wg_peer` and its `noise_handshake`, `struct allowedips` and
`struct allowedips_node`. Pointers are identities into finite stores; list
heads are ordered lists of identities.

Omitted, as cut points: the UDP sockets, the timer wheel (the timers'
`expires` is mirrored, D3), NAPI, `dst_cache`, and the device's cookie
encryption key (BLAKE2s outputs that nothing on the modeled paths observes).
Keypairs live in the device's keypair store (`Device.keypairs`), referenced
by identity from the peer's `keypairs` slots and the index hashtable. The public-key hashtable is a map:
its bucketing uses a random `siphash` key, so bucket order is unobservable.
-/

namespace Leanux.WG
open Std

abbrev PeerId := Nat
abbrev NodeId := Nat

/-- Where a trie node hangs: `parent_bit_packed`. The low bits are 2 for a
    root pointer, or the bit (0 or 1) of the parent node's child slot. -/
inductive Slot where
  | root4 | root6
  | child (parent : NodeId) (bit : Nat)
  deriving Repr, BEq

/-- `struct allowedips_node`. `bits` holds the key as `swap_endian` produced
    it (the address as a big-endian integer), unmasked; `read_node` masks. -/
structure AipNode where
  peer : Option PeerId
  bit : Array (Option NodeId)   -- bit[2]
  cidr : Nat
  bitlen : Nat                  -- 32 or 128
  bits : Nat
  parent : Slot
  deriving Repr, BEq

/-- `struct allowedips`. -/
structure AllowedIps where
  root4 : Option NodeId := none
  root6 : Option NodeId := none
  seq : Nat := 1
  deriving Repr, BEq

/-- `struct endpoint`: `sa_family` 0 means no endpoint. -/
structure Endpoint where
  family : Nat      -- AF_INET = 2, AF_INET6 = 10
  addr : Nat
  port : Nat
  /-- `src4`/`src6` (the local address a received packet was sent to),
      `src_if4`, and IPv6's `sin6_scope_id`: zero unless learned from an skb. -/
  src : Nat := 0
  srcIf : Nat := 0
  scope : Nat := 0
  deriving Repr, BEq

/-- What a received skb says about its origin (`wg_socket_endpoint_from_skb`):
    the IP family, source address and UDP port, destination address, and
    arrival interface; and the outer header's DS field
    (`ip_tunnel_get_dsfield`, D2 stream B: `PACKET_CB(skb)->ds` on receive). -/
structure SkbSource where
  family : Nat
  saddr : Nat
  sport : Nat
  daddr : Nat
  iif : Nat
  tos : Nat := 0
  deriving Repr, BEq

/-- `enum index_hashtable_type`. -/
inductive IndexKind where
  | handshake | keypair
  deriving Repr, BEq, DecidableEq

/-- A keypair's identity in the device's keypair store. -/
abbrev KeypairId := Nat

/-- An `index_hashtable_entry` in the device's index hashtable: a peer's
    handshake or one of its keypairs, under a random index. -/
structure IndexEntry where
  index : Nat
  peer : PeerId
  kind : IndexKind
  /-- For a keypair entry, which keypair (an initiator peer can hold a
      current and a next keypair, each with its own entry). -/
  keypair : Option KeypairId := none
  deriving Repr, BEq

/-- `struct noise_symmetric_key`. -/
structure SymmetricKey where
  key : List UInt8 := List.replicate 32 0
  birthdate : Int := 0
  isValid : Bool := false
  deriving Repr, BEq

/-- `struct noise_replay_counter` (noise.h): the highest counter seen plus
    one, and the RFC 6479 bitmap as `COUNTER_BITS_TOTAL / BITS_PER_LONG` =
    128 words of 64 bits. -/
structure ReplayCounter where
  counter : Nat := 0
  backtrack : Array Nat := Array.replicate 128 0
  deriving Repr, BEq

/-- `struct noise_keypair` (noise.h): the session keys and counters. -/
structure Keypair where
  sending : SymmetricKey := {}
  receiving : SymmetricKey := {}
  /-- `sending_counter` (`atomic64`): the next nonce is its value. -/
  sendingCounter : Nat := 0
  iAmTheInitiator : Bool := false
  remoteIndex : Nat := 0
  /-- The keypair's `kref`. -/
  refcount : Nat := 1
  internalId : Nat := 0
  peer : PeerId := 0
  /-- `receiving_counter` (D2). -/
  receivingCounter : ReplayCounter := {}
  deriving Repr, BEq

/-- `enum packet_state` (queueing.h). -/
inductive PacketState where
  | uncrypted | crypted | dead
  deriving Repr, BEq, DecidableEq

/-- An outgoing skb before encryption (D2): the IP packet `wg_xmit`
    received (empty for a keepalive), its `CHECKSUM_PARTIAL` state as
    (`csum_start`, `csum_offset`) offsets into `bytes`, or `none` when the
    checksum is complete or absent, and `PACKET_CB(skb)->mtu`. -/
structure Packet where
  bytes : List UInt8 := []
  csum : Option (Nat × Nat) := none
  mtu : Nat := 0
  deriving Repr, BEq

/-- A data packet on its way out: the plaintext packet, the keypair and
    nonce it was given, its state, and (once encrypted) the message bytes.
    One ring item is a list of these (`create_data` gives the keypair to the
    first; all share it). -/
structure DataPacket where
  peer : PeerId
  keypair : KeypairId
  nonce : Nat
  plaintext : Packet := {}
  /-- `PACKET_CB(skb)->ds` (D2 stream A): the outer DS field
      `ip_tunnel_ecn_encap` computed, which `send4`/`send6` (a cut) use. -/
  ds : Nat := 0
  state : PacketState := .uncrypted
  bytes : List UInt8 := []
  deriving Repr, BEq

/-- A received data message on its way in (D2): its keypair (from the index
    lookup), the counter it carries (`PACKET_CB(skb)->nonce`), the bytes
    (the message, then the decrypted plaintext), its state, and the outer
    headers' origin (`wg_socket_endpoint_from_skb`). -/
structure RxPacket where
  peer : PeerId
  keypair : KeypairId
  nonce : Nat := 0
  bytes : List UInt8
  state : PacketState := .uncrypted
  source : SkbSource
  /-- `PACKET_CB(skb)->ds`: the outer header's DS field (D2 stream B). -/
  ds : Nat := 0
  deriving Repr, BEq

/-- `struct wg_peer` with the parts of its `noise_handshake` on this path. -/
structure Peer where
  remoteStatic : Key
  presharedKey : Key
  precomputedStaticStatic : Key
  endpoint : Option Endpoint := none
  persistentKeepaliveInterval : Nat := 0
  allowedipsList : List NodeId := []
  isDead : Bool := false
  refcount : Nat := 1
  internalId : Nat
  /-- `staged_packet_queue`, oldest first; a keepalive is an empty packet.
      Packets wait here for a session. -/
  staged : List Packet := []
  /-- `transmit_handshake_work` is queued and the worker has not run: the
      worker's timing is not determined, so what reads its state is outside
      the domain until `wg_observe` waits for it. -/
  handshakePending : Bool := false
  /-- `last_sent_handshake` (ns of coarse boot time, s64): from recorded
      clock reads (`wg_noise_reset_last_sent_handshake` sets it
      `REKEY_TIMEOUT + 1` seconds in the past). -/
  lastSentHandshake : Int := 0
  /-- `handshake.last_initiation_consumption` (ns, s64). -/
  lastInitiationConsumption : Int := 0
  txBytes : Nat := 0
  /-- `handshake.state`: ZEROED 0, CREATED_INITIATION 1, CONSUMED_INITIATION 2,
      CREATED_RESPONSE 3, CONSUMED_RESPONSE 4. -/
  handshakeState : Nat := 0
  /-- `handshake.latest_timestamp` (TAI64N, compared with memcmp). -/
  latestTimestamp : List UInt8 := List.replicate 12 0
  /-- `handshake.remote_index`, the initiator's sender index. -/
  remoteIndex : Nat := 0
  /-- `keypairs.current_keypair`, `previous_keypair`, `next_keypair` in the
      device's keypair store. A keypair's index entry (it replaced the
      handshake's) stays in the index hashtable until the keypair is put
      with `unreference_now` or released. -/
  keypairCurrent : Option KeypairId := none
  keypairPrevious : Option KeypairId := none
  keypairNext : Option KeypairId := none
  /-- `walltime_last_handshake` (`struct timespec64`, a recorded clock read):
      the dump's `last_handshake`. -/
  walltimeLastHandshake : List UInt8 := List.replicate 16 0
  /-- `serial_work_cpu`: `nr_cpumask_bits` until the first transmit
      (`wg_cpumask_choose_online`). -/
  serialWorkCpu : Option Nat := none
  /-- `tx_queue`: ring items handed to the per-peer transmit worker, oldest
      first. An item is a staged list (`skb->next`), nonempty; its first
      packet carries the item's `PACKET_CB` state (D2 stream A). -/
  txQueue : List (List DataPacket) := []
  /-- `rx_queue` (`wg_prev_queue`), oldest first, and whether its NAPI poll
      is scheduled (`napi_schedule` without a run yet) (D2). -/
  rxQueue : List RxPacket := []
  napiScheduled : Bool := false
  /-- The five `struct timer_list` (peer.h:53-55), D3 interface
      (docs/2026-10-05-d3-timers.md, section 5.1): `some expires` (absolute
      64-bit `jiffies`, never truncated) while the timer is pending, `none`
      otherwise; `timer_pending` is `isSome` (`Peer.timerPending`). The
      expiry comes from the kind-303 arm record once the mirror consumes it
      (stream M); until then it is the nominal `jiffies + delay`
      (`WG.armTimer`), which nothing reads. -/
  timerRetransmitHandshake : Option Nat := none
  timerSendKeepalive : Option Nat := none
  timerNewHandshake : Option Nat := none
  timerZeroKeyMaterial : Option Nat := none
  timerPersistentKeepalive : Option Nat := none
  /-- `timer_handshake_attempts` (peer.h:56). -/
  timerHandshakeAttempts : Nat := 0
  /-- `timer_need_another_keepalive` and `sent_lastminute_handshake`
      (peer.h:57-59). -/
  timerNeedAnotherKeepalive : Bool := false
  sentLastminuteHandshake : Bool := false
  rxBytes : Nat := 0
  /-- `handshake.ephemeral_private`, `remote_ephemeral`, `chaining_key` and
      `hash` (zeroed by `handshake_zero`). -/
  ephemeralPrivate : Key := List.replicate 32 0
  remoteEphemeral : Key := List.replicate 32 0
  chainingKey : List UInt8 := List.replicate 32 0
  hash : List UInt8 := List.replicate 32 0
  /-- `latest_cookie.message_mac1_key` (`wg_cookie_checker_precompute_peer_keys`),
      `last_mac1_sent` and `have_sent_mac1`. -/
  cookieMac1Key : Key := List.replicate 32 0
  lastMac1Sent : List UInt8 := List.replicate 16 0
  haveSentMac1 : Bool := false
  /-- `latest_cookie.cookie_decryption_key` (`wg_cookie_checker_precompute_peer_keys`,
      cookie.c:63-64), and the cookie a cookie reply delivered
      (`wg_cookie_message_consume`, cookie.c:224-226): `cookie`, `birthdate`
      (ns of coarse boot time, a recorded clock read) and `is_valid`. -/
  cookieDecryptionKey : Key := List.replicate 32 0
  cookie : List UInt8 := List.replicate 16 0
  cookieBirthdate : Int := 0
  cookieIsValid : Bool := false
  deriving Repr, BEq

/-- A peer's five timers (`struct wg_peer`, peer.h:53-55), in the order of
    their callbacks in timers.c. -/
inductive PeerTimer where
  | retransmitHandshake | sendKeepalive | newHandshake | zeroKeyMaterial | persistentKeepalive
  deriving Repr, BEq, DecidableEq

def PeerTimer.all : List PeerTimer :=
  [.retransmitHandshake, .sendKeepalive, .newHandshake, .zeroKeyMaterial, .persistentKeepalive]

/-- The timer's `expires` while pending. -/
def Peer.timer (p : Peer) : PeerTimer → Option Nat
  | .retransmitHandshake => p.timerRetransmitHandshake
  | .sendKeepalive => p.timerSendKeepalive
  | .newHandshake => p.timerNewHandshake
  | .zeroKeyMaterial => p.timerZeroKeyMaterial
  | .persistentKeepalive => p.timerPersistentKeepalive

/-- `timer_pending(&peer->timer_x)` (timer.h:145-148): hashed in a bucket. -/
def Peer.timerPending (p : Peer) (t : PeerTimer) : Bool := (p.timer t).isSome

def Peer.setTimer (p : Peer) (t : PeerTimer) (v : Option Nat) : Peer :=
  match t with
  | .retransmitHandshake => { p with timerRetransmitHandshake := v }
  | .sendKeepalive => { p with timerSendKeepalive := v }
  | .newHandshake => { p with timerNewHandshake := v }
  | .zeroKeyMaterial => { p with timerZeroKeyMaterial := v }
  | .persistentKeepalive => { p with timerPersistentKeepalive := v }

/-- `struct noise_static_identity`. -/
structure StaticIdentity where
  hasIdentity : Bool := false
  staticPrivate : Key := List.replicate 32 0
  staticPublic : Key := List.replicate 32 0
  deriving Repr, BEq

/-- `struct wg_device`: the fixture's `wg0` (created down before the
    trace), or one a trace created (`wg_newlink`, L). -/
structure Device where
  ifindex : Nat
  ifname : String
  running : Bool := false
  /-- `sock4`, `sock6` (L): the bound UDP sockets, by their port; `none`
      while down (NULL). `wg_socket_reinit` sets `incoming_port` from
      `sock4`. -/
  sock4 : Option Nat := none
  sock6 : Option Nat := none
  /-- `creating_net` is set (L): cleared only by `wg_destruct`; the operand
      of `wg_socket_init`'s `-ENONET` arm. -/
  creatingNet : Bool := true
  /-- `cookie_checker.secret` and `secret_birthdate` (L, `wg_cookie_checker_init`)
      and the public-key hashtable's siphash key (`wg_pubkey_hashtable_alloc`),
      from their records; zeros for the fixture's wg0, created before the
      trace (unknown). -/
  cookieSecret : List UInt8 := List.replicate 32 0
  cookieSecretBirthdate : Int := 0
  /-- `cookie_checker.cookie_encryption_key` (E-B): `blake2s("cookie--" ‖
      static_public)` (`wg_cookie_checker_precompute_device_keys`, cookie.c:48),
      under which `wg_cookie_message_create` seals a cookie reply; zero until an
      identity is set. -/
  cookieEncryptionKey : List UInt8 := List.replicate 32 0
  pubkeyHashKey : List UInt8 := List.replicate 16 0
  /-- `dev->stats` counters. -/
  txErrors : Nat := 0
  txDropped : Nat := 0
  rxErrors : Nat := 0
  rxFrameErrors : Nat := 0
  rxLengthErrors : Nat := 0
  /-- `cookie_checker.message_mac1_key`: zero until an identity is set. -/
  mac1Key : Key := List.replicate 32 0
  /-- `handshake_queue.last_cpu`, initialized to -1 (queueing.c:31). -/
  handshakeLastCpu : Int := -1
  /-- `handshake_queue.ring`: queued handshake messages, oldest first; its
      length is `handshake_queue_len`. -/
  handshakeQueue : List (List UInt8 × SkbSource) := []
  staticIdentity : StaticIdentity := {}
  incomingPort : Nat := 0
  fwmark : Nat := 0
  /-- `device_update_gen`: 1 at `wg_newlink` (device.c:323). -/
  deviceUpdateGen : Nat := 1
  numPeers : Nat := 0
  peerList : List PeerId := []
  peers : TreeMap PeerId Peer := {}
  /-- The public-key hashtable, as a map from key to peer. -/
  peerHashtable : List (Key × PeerId) := []
  peerAllowedips : AllowedIps := {}
  nodes : TreeMap NodeId AipNode := {}
  nextNode : NodeId := 0
  nextPeer : PeerId := 0
  /-- The index hashtable's entries, newest first (`hlist_add_head_rcu`); a
      bucket is the entries whose index has the same low 13 bits, in this
      order. -/
  indexTable : List IndexEntry := []
  /-- `handshake_send_wq`: peers whose `transmit_handshake_work` is queued,
      oldest first. -/
  sendWorkQueue : List PeerId := []
  /-- The keypair store (`kzalloc`ed keypairs that are still referenced). -/
  keypairs : TreeMap KeypairId Keypair := {}
  nextKeypairId : KeypairId := 0
  /-- `encrypt_queue.last_cpu` (`wg_cpumask_next_online`), and the ring
      items queued for the encrypt worker, oldest first: each a staged list
      of packets (D2 stream A). -/
  encryptLastCpu : Int := -1
  encryptQueue : List (List DataPacket) := []
  /-- Peers whose `transmit_packet_work` is queued, oldest first. -/
  txWorkQueue : List PeerId := []
  /-- `decrypt_queue.last_cpu` and the messages queued for the decrypt worker,
      oldest first (D2). -/
  decryptLastCpu : Int := -1
  decryptQueue : List RxPacket := []
  /-- D3: peers whose `clear_peer_work` (`wg_queued_expired_zero_key_material`)
      is queued on `handshake_send_wq`, oldest first
      (docs/2026-10-05-d3-timers.md, section 5.4). -/
  clearWorkQueue : List PeerId := []
  deriving BEq

def AF_INET : Nat := 2
def AF_INET6 : Nat := 10
def MESSAGE_HANDSHAKE_INITIATION_LEN : Nat := 148

end Leanux.WG
