import Leanux.WG.Curve25519
import Std.Data.TreeMap

/-!
# WireGuard state (drivers/net/wireguard)

Shaped like the C structures of the configuration path: `struct wg_device`,
`struct wg_peer` and its `noise_handshake`, `struct allowedips` and
`struct allowedips_node`. Pointers are identities into finite stores; list
heads are ordered lists of identities.

Omitted, as cut points of the configuration path with the device down: the UDP
sockets, timers, work queues, NAPI, packet queues, keypairs (none exist before
a handshake), the index hashtable, `dst_cache`, and the cookie keys (BLAKE2s
outputs that nothing on this path observes). The public-key hashtable is a map:
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
  /-- `staged_packet_queue`'s length: packets wait here for a session. -/
  staged : Nat := 0
  /-- `transmit_handshake_work` is queued and the worker has not run: the
      worker's timing is not determined, so what reads its state is outside
      the domain until `wg_observe` waits for it. -/
  handshakePending : Bool := false
  /-- Whether `last_sent_handshake` is older than `REKEY_TIMEOUT`. It starts
      expired (`wg_noise_reset_last_sent_handshake`), and the worker makes it
      current; traces are bounded well below `REKEY_TIMEOUT`. -/
  lastSentExpired : Bool := true
  txBytes : Nat := 0
  deriving Repr, BEq

/-- `struct noise_static_identity`. -/
structure StaticIdentity where
  hasIdentity : Bool := false
  staticPrivate : Key := List.replicate 32 0
  staticPublic : Key := List.replicate 32 0
  deriving Repr, BEq

/-- `struct wg_device` (the fixture's `wg0`, created down). -/
structure Device where
  ifindex : Nat
  ifname : String
  running : Bool := false
  /-- `dev->stats` transmit counters. -/
  txErrors : Nat := 0
  txDropped : Nat := 0
  staticIdentity : StaticIdentity := {}
  incomingPort : Nat := 0
  fwmark : Nat := 0
  deviceUpdateGen : Nat := 0
  numPeers : Nat := 0
  peerList : List PeerId := []
  peers : TreeMap PeerId Peer := {}
  /-- The public-key hashtable, as a map from key to peer. -/
  peerHashtable : List (Key × PeerId) := []
  peerAllowedips : AllowedIps := {}
  nodes : TreeMap NodeId AipNode := {}
  nextNode : NodeId := 0
  nextPeer : PeerId := 0
  deriving BEq

/-- The fixture's UDP listeners (127.0.0.1 and ::1 at `LISTEN_PORT`): the
    lengths of the datagrams waiting in each receive queue. -/
structure Listeners where
  v4 : List Nat := []
  v6 : List Nat := []
  deriving Repr, BEq

def AF_INET : Nat := 2
def AF_INET6 : Nat := 10
def LISTEN_PORT : Nat := 51999
def MESSAGE_HANDSHAKE_INITIATION_LEN : Nat := 148

end Leanux.WG
