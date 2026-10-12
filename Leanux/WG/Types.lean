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
  /-- W1: IPv6's `sin6_flowinfo`, copied by `set_peer` with the whole
      `sockaddr_in6` (netlink.c:444-446) and returned by the dump; never
      compared (`endpoint_eq`, socket.c:258-271) and zeroed by
      `wg_socket_endpoint_from_skb`. -/
  flowinfo : Nat := 0
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

/-- The identity of an skb on its way out or in (simulation-target review,
    section 4.2): the device ring, the peer's `prev_queue`, a peeked head and
    a worker's local name the one object in the device's store
    (`Device.txSkbs`, `Device.rxSkbs`), whose state publication changes once. -/
abbrev SkbId := Nat

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

/-- `SMP_CACHE_BYTES` (`CONFIG_X86_L1_CACHE_SHIFT` 6): the cache line the
    ring's batch is sized by. -/
def SMP_CACHE_BYTES : Nat := 64
/-- `MAX_QUEUED_PACKETS` (messages.h:53): the crypt rings' size
    (`wg_packet_queue_init`) and the bound of a peer's `prev_queue`. -/
def MAX_QUEUED_PACKETS : Nat := 1024

/-- `struct ptr_ring` (include/linux/ptr_ring.h:30-40) as data (simulation-
    target review, section 4.1): the producer cursor, the consumer head (the
    next valid entry) and tail (the next entry to invalidate), the size, the
    batch, and the slots' occupancy. Consumed slots stay occupied until the
    batch clears them, so the full test is occupancy, not the count. Its
    operations are in `Leanux/WG/PtrRing.lean`. -/
structure PtrRing (α : Type) where
  size : Nat
  /-- `r->batch` (:474-484): `SMP_CACHE_BYTES * 2 / sizeof(void *)`, or 1
      when that exceeds half the size or is 0. -/
  batch : Nat
  producer : Nat := 0
  consumerHead : Nat := 0
  consumerTail : Nat := 0
  slots : Array (Option α)
  deriving BEq

/-- `ptr_ring_init` (:470-486) of `size` entries, every slot free. -/
def PtrRing.init (size : Nat) : PtrRing α :=
  let batch := SMP_CACHE_BYTES * 2 / 8
  { size, batch := if batch > size / 2 || batch == 0 then 1 else batch,
    slots := Array.replicate size none }

instance : Inhabited (PtrRing α) := ⟨PtrRing.init 0⟩

/-- `struct prev_queue` (queueing.h:34-39, queueing.c:50-106) as data (W7
    stream B, docs/2026-10-06-w4-w7-transmit-bulk.md 5.1): the items
    enqueued and not yet dequeued (`count`, oldest first), whether `tail`
    is the stub (`queue->tail == STUB(queue)`), and the item a consumer
    peeked (`queue->peeked`: dequeued, not yet dropped). Its operations are
    in `Leanux/WG/PrevQueue.lean`. -/
structure PrevQueue (α : Type) where
  items : List α := []
  tailIsStub : Bool := true
  peeked : Option α := none
  deriving Repr, BEq

instance : Inhabited (PrevQueue α) := ⟨{}⟩

/-- W9: a peer's `endpoint_cache` (`struct dst_cache`, one CPU: one
    per-cpu slot): `reset_ts` and the slot's `refresh_ts`, both `jiffies`
    the kernel records (kind 306), and the cached route with the source
    address it was made with and the generation of the tables then
    (`rt_genid` / the IPv6 sernum: the dst's validity check). -/
structure DstSlot where
  src : Nat
  gen : Nat
  dev : Nat
  deriving Repr, BEq

structure DstCache where
  resetTs : Nat := 0
  refreshTs : Nat := 0
  slot : Option DstSlot := none
  deriving Repr, BEq

/-- `struct wg_peer` with the parts of its `noise_handshake` on this path. -/
structure Peer where
  remoteStatic : Key
  presharedKey : Key
  precomputedStaticStatic : Key
  endpoint : Option Endpoint := none
  /-- W9: `endpoint_cache` (`dst_cache_init` in `wg_peer_create`). -/
  dstCache : DstCache := {}
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
  /-- `tx_queue` (`struct prev_queue`, W7 stream B): ring items handed to
      the per-peer transmit worker, oldest first. An item is a staged list
      (`skb->next`) of skb ids, nonempty; its first skb carries the item's
      `PACKET_CB` state (D2 stream A), in `Device.txSkbs`. -/
  txQueue : PrevQueue (List SkbId) := {}
  /-- `rx_queue` (`struct prev_queue`), oldest first, skb ids into
      `Device.rxSkbs`, and whether its NAPI poll is scheduled
      (`napi_schedule` without a run yet) (D2). -/
  rxQueue : PrevQueue SkbId := {}
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
  /-- W8: `__LINK_STATE_NOCARRIER` inverted (never set by WireGuard, so the
      device starts with carrier); `wg_netns_pre_exit`'s `netif_carrier_off`
      clears it. Observable only on an up device (W8b). -/
  carrier : Bool := true
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
  /-- The device tstats (`NETDEV_PCPU_STAT_TSTATS`, `update_rx_stats`,
      receive.c:19-23): every honest data message and keepalive (W5, 2.6).
      The driver adds no transmit count. -/
  rxPackets : Nat := 0
  rxBytes : Nat := 0
  /-- The transmit side of the tstats: `iptunnel_xmit_stats` in
      `iptunnel_xmit` / `ip6tunnel_xmit` (`udp_tunnel_xmit_skb`,
      `udp_tunnel6_xmit_skb` with `skb->dev = wg->dev`) counts every
      datagram wg0's sockets send and its length (W5, 2.6: the design's
      "no transmit count" was wrong; the first run showed `tx_packets` 1,
      `tx_bytes` 148 after one initiation [AGENT, W5+W6 fork]). -/
  txPackets : Nat := 0
  txBytes : Nat := 0
  /-- W4 (docs/2026-10-06-w4-w7-transmit-bulk.md, section 4): `dev->mtu`,
      1420 from `wg_setup` (device.c:296), moved by `SIOCSIFMTU` (`setMtu`);
      whether wg0 has an `in_device` (gone below 68) and an `inet6_dev` (gone
      below 1280), the tests of `wg_open` (device.c:39, 47). -/
  mtu : Nat := 1420
  inet4Dev : Bool := true
  inet6Dev : Bool := true
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
  /-- `handshake_queue.ring`: queued handshake messages, oldest first. -/
  handshakeQueue : List (List UInt8 × SkbSource) := []
  /-- `handshake_queue_len` (device.h), the atomic counter beside the ring:
      incremented by the producer after a successful produce (receive.c:567)
      and decremented by the worker after each packet (receive.c:215), so it
      exceeds the ring's occupancy by one while a packet is processed. The
      under-load test reads it (receive.c:112), the busy test too (:554);
      the ring-full test reads the ring. -/
  handshakeQueueLen : Nat := 0
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
  encryptQueue : PtrRing (List SkbId) := PtrRing.init MAX_QUEUED_PACKETS
  /-- Peers whose `transmit_packet_work` is queued, oldest first. -/
  txWorkQueue : List PeerId := []
  /-- `decrypt_queue.last_cpu` and the messages queued for the decrypt worker,
      oldest first (D2). -/
  decryptLastCpu : Int := -1
  decryptQueue : PtrRing SkbId := PtrRing.init MAX_QUEUED_PACKETS
  /-- The skb store (review 4.2): every outgoing data skb from its
      `PACKET_CB` assignment in `wg_packet_send_staged_packets` to its
      `kfree_skb` (or its consumption by the stack), and every incoming data
      skb from `wg_packet_consume_data` to its free, owned once; the queues
      hold ids. `nextSkb` numbers them. -/
  txSkbs : TreeMap SkbId DataPacket := {}
  rxSkbs : TreeMap SkbId RxPacket := {}
  nextSkb : SkbId := 0
  /-- D3: peers whose `clear_peer_work` (`wg_queued_expired_zero_key_material`)
      is queued on `handshake_send_wq`, oldest first
      (docs/2026-10-05-d3-timers.md, section 5.4). -/
  clearWorkQueue : List PeerId := []
  deriving BEq

def AF_INET : Nat := 2
def AF_INET6 : Nat := 10
def MESSAGE_HANDSHAKE_INITIATION_LEN : Nat := 148

end Leanux.WG
