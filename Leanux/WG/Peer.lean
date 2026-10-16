import Leanux.WG.AllowedIps
import Leanux.Kernel.Refcount
import Leanux.WG.Blake2s
import Leanux.WG.Socket

/-!
# drivers/net/wireguard/peer.c, peerlookup.c (public keys) and the noise.c
# static-identity functions on the configuration path

Cut points (no mirror state or decisions): `dst_cache_init`/`_reset`, timers,
work items, packet queues, NAPI add/enable/disable/del, `synchronize_net`,
`flush_workqueue`, `call_rcu` freeing, the cookie keys (BLAKE2s), and
`endpoint_eq` (a pure equality predicate). The keypair store's references and
peer removal, which clears a peer's keypairs, are in `Leanux/WG/Keypair.lean`.
-/

namespace Leanux.WG
open Leanux

def MAX_PEERS_PER_DEVICE : Nat := 1 <<< 20

/-- wg_peer_get (peer.h): `kref_get(&peer->refcount)`. -/
def peerGet (pid : PeerId) : M Unit := do
  requireNotPending pid "a reference count the handshake worker also changes"
  let p ← getPeer pid
  refcountInc p.refcount
  setPeer pid { p with refcount := p.refcount + 1 }

/-- `entry->peer` of an owner's embedded `index_hashtable_entry`, read
    through the owner. -/
def IndexOwner.peerWord : IndexOwner → M (Option PeerId)
  | .handshake pid => return (← getPeer pid).handshakeEntryPeer
  | .keypair kp => return (← getKeypair kp).peer

/-- A store into `entry->peer` (peerlookup.c:218). -/
def IndexOwner.setPeerWord (o : IndexOwner) (v : Option PeerId) : M Unit := do
  match o with
  | .handshake pid => setPeer pid { (← getPeer pid) with handshakeEntryPeer := v }
  | .keypair kp => setKeypair kp { (← getKeypair kp) with peer := v }

/-- A dereference of `entry->peer` (`entry.peer->device`, `wg_peer_get(entry.peer)`,
    `PACKET_PEER(skb)->...`): on NULL the C dereferences a NULL pointer, which
    the mirror does not model. NULL is stored only by a failed get, which
    this configuration never reaches (docs/2026-10-05-l-lifecycle.md 16.6). -/
def IndexOwner.peerDeref (o : IndexOwner) : M PeerId := do
  let some pid ← o.peerWord | unsupported "entry->peer is NULL: the C dereferences it"
  return pid

/-- `hlist_del_init_rcu(&entry->index_hash)` (rculist.h:182-188): the
    `hlist_unhashed` test is the decision `d`, true when the entry is in the
    table; the unhash leaves it absent either way. -/
private def unhashEntry (d : Decision) (hashed : IndexEntry → Bool) : M Unit := do
  _ ← branch d ((← getDev).indexTable.any hashed)
  modifyDev fun dev => { dev with indexTable := dev.indexTable.filter fun e => !hashed e }

/-- wg_index_hashtable_remove (peerlookup.c:192-198) of an owner's entry:
    `hlist_del_init_rcu`, a no-op if unhashed. -/
def indexRemove (owner : IndexOwner) : M Unit :=
  unhashEntry .idxRemoveHashed (·.owner == owner)

/-- wg_peer_put (peer.c:223-228) and kref_release (200-221): the release
    removes the handshake's index entry (which `peer_remove_after_dead`
    leaves for it); the staged-packet purge and the `call_rcu` free are cut
    points; the peer leaves the store. -/
def peerPut (peer : Option PeerId) : M Unit := do
  if ← branch .peerPutNull peer.isNone then return
  let some pid := peer | invariant "unreachable"
  requireNotPending pid "a reference count the handshake worker also changes"
  let p ← getPeer pid
  setPeer pid { p with refcount := p.refcount - 1 }
  if ← branch .peerKrefPutReleased (← refcountDecAndTest p.refcount) then
    indexRemove (.handshake pid)   -- `&peer->handshake.entry` (peer.c:211-212)
    -- rcu_release's `WARN_ON(wg_prev_queue_peek(&tx_queue) || wg_prev_queue_peek(&rx_queue))`
    -- (peer.c:191): a queued batch holds a reference (Send.lean, Receive.lean),
    -- so a release with packets queued is a reference slip; the C warns and
    -- frees, the mirror stops here rather than at a later dangling id (the
    -- Peer audit's F3)
    if p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty then
      invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)"
    -- wg_packet_purge_staged_packets: DEV_STATS_ADD(tx_dropped, qlen)
    modifyDev fun d => { d with txDropped := d.txDropped + p.staged.length, peers := d.peers.erase pid }
    -- B3: a released peer has no pending timer (wg_timers_stop ran at its
    -- removal, timers.c:235-243); a wheel entry left here is a mirror defect
    if let some t := PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome) then
      invariant s!"peer {pid} released with its {repr t} timer pending"
    -- the peer's work structs and timers are freed with it (rcu_free): their
    -- dispatch identities end here (docs/2026-10-11-dispatch-order.md, 4)
    retirePeerUnits pid

/-- wg_noise_precompute_static_static (noise.c:47-57). -/
def precomputeStaticStatic (pid : PeerId) : M Unit := do
  requireNotPending pid "recomputing the static-static key"
  let identity := (← getDev).staticIdentity
  let p ← getPeer pid
  -- `!has_identity || !curve25519(precomputed, static_private, remote_static)`
  let zero ← do
    if ← branch .precomputeNoIdentity !identity.hasIdentity then pure true
    else
      let (out, nonNull) := curve25519 identity.staticPrivate p.remoteStatic
      setPeer pid { p with precomputedStaticStatic := out }
      branch .precomputeNullPoint !nonNull
  if zero then setPeer pid { (← getPeer pid) with precomputedStaticStatic := List.replicate 32 0 }

/-- `curve25519_generate_public` (include/crypto/curve25519.h:46-59): the
    public key if one is written (the null-secret arm returns before writing
    `pub`), and the result. -/
def generatePublic (secret : Key) : M (Option Key × Bool) := do
  if ← branch .genPublicNullSecret (secret == nullPoint) then return (none, false)
  let (pub, nonNull) := curve25519 secret basePoint
  return (some pub, nonNull)

/-- wg_noise_set_static_identity_private_key (noise.c:294-303). -/
def setStaticIdentityPrivateKey (privateKey : Key) : M Unit := do
  -- the handshake worker reads has_identity
  for pid in (← getDev).peerList do requireNotPending pid "changing the device identity"
  let clamped := clamp privateKey   -- memcpy; curve25519_clamp_secret
  let (pub, has) ← generatePublic privateKey
  modifyDev fun d => { d with staticIdentity := { hasIdentity := has, staticPrivate := clamped,
                                                  staticPublic := pub.getD d.staticIdentity.staticPublic } }

/-- wg_cookie_checker_precompute_device_keys (cookie.c:45-59): the keys are
    BLAKE2s outputs nothing on this path observes. -/
def cookiePrecomputeDeviceKeys : M Unit := do
  let identity := (← getDev).staticIdentity
  -- precompute_key(cookie_encryption_key, static_public, "cookie--") and
  -- precompute_key(message_mac1_key, static_public, "mac1----"); E-B reads the
  -- cookie encryption key when wg0 creates a cookie reply
  let (encKey, mac1Key) ← do
    if ← branch .cookieDeviceHasIdentity identity.hasIdentity then
      pure (blake2s 32 [] ("cookie--".toUTF8.toList ++ identity.staticPublic),
            blake2s 32 [] ("mac1----".toUTF8.toList ++ identity.staticPublic))
    else pure (List.replicate 32 0, List.replicate 32 0)
  modifyDev fun d => { d with cookieEncryptionKey := encKey, mac1Key := mac1Key }

/-- wg_noise_keypair_put (noise.c:131-140) on the NULL keypairs of a peer that
    never completed a handshake. -/
def keypairPutNull : M Unit := do
  if ← branch .keypairPutNull true then return
  unsupported "wg_noise_keypair_put of a live keypair"

/-! ### The index hashtable (peerlookup.c) -/

def INDEX_HASHTABLE_BITS : Nat := 13

/-- `index_bucket` (peerlookup.c:73-81): the entries under the same masked
    index, in list order. -/
def indexBucket (index : Nat) : M (List IndexEntry) := do
  let mask := 2 ^ INDEX_HASHTABLE_BITS
  return (← getDev).indexTable.filter (·.index % mask == index % mask)

/-- Whether an owner's entry is hashed (`!hlist_unhashed`). -/
def indexHashed (owner : IndexOwner) : M Bool :=
  return (← getDev).indexTable.any (·.owner == owner)

/-- A walk over a bucket for `index`, reporting the loop and the compare:
    whether some entry has this index. -/
private def bucketHas (walk collide : Decision) (index : Nat) : M Bool := do
  for e in ← indexBucket index do
    _ ← branch walk true
    if ← branch collide (e.index == index) then return true
  _ ← branch walk false
  return false

/-- wg_index_hashtable_insert (peerlookup.c:109-153): a fresh random index
    (a recorded hidden input) not in use, inserted at the head. -/
def indexInsert (owner : IndexOwner) : M Nat := do
  -- `hlist_del_init_rcu(&entry->index_hash)` first (peerlookup.c:125)
  unhashEntry .idxInsertHashed (·.owner == owner)
  -- `goto search_unused_slot` draws again; nothing else inserts meanwhile
  -- (one CPU), so the locked walk agrees with the unlocked one. The C loop
  -- is unbounded; the draws are records, so the loop is record-driven
  -- (review item 7): it ends when the records do
  for _ in [0:(← recordBudget)] do
    let draw ← hidden .indexDraw
    let index := draw.foldr (fun b acc => acc * 256 + b.toNat) 0   -- __le32
    if ← bucketHas .idxInsWalk1 .idxInsCollide1 index then continue
    -- the locked walk's collision (stolen meanwhile, peerlookup.c:148) needs
    -- a concurrent insert
    if ← bucketHas .idxInsWalk2 .idxInsCollide2 index then unsupported "an index stolen during insertion"
    modifyDev fun d => { d with indexTable := { index, owner } :: d.indexTable }
    return index
  budgetExhausted "index draws"

/-- wg_index_hashtable_replace (peerlookup.c:166-190) of a peer's handshake
    entry by its new keypair's, in place: the keypair's entry takes the
    handshake's index and list position, and the handshake's is unhashed.
    Whether the handshake entry was hashed. -/
def indexReplaceHandshake (pid : PeerId) (kp : KeypairId) : M Bool := do
  let hashed ← indexHashed (.handshake pid)
  if ← branch .idxReplaceUnhashed !hashed then return false
  -- `new->index = old->index; hlist_replace_rcu(...)`: the keypair's own
  -- entry, with its own peer word, takes the index and the list position
  modifyDev fun d => { d with indexTable := d.indexTable.map fun e =>
    if e.owner == (.handshake pid) then { e with owner := .keypair kp } else e }
  return true

def NSEC_PER_SEC : Int := 1000000000
/-- `NSEC_PER_SEC` in the age test's `s64` (review item 8). -/
def NSEC_PER_SEC64 : Int64 := 1000000000
def REKEY_TIMEOUT : Nat := 5
def KEEPALIVE_TIMEOUT : Nat := 10

/-- wg_noise_reset_last_sent_handshake (noise.h:100-104): the recorded coarse
    boot time, `REKEY_TIMEOUT + 1` seconds back, in `u64` (held as the s64
    the age test casts it to). -/
def resetLastSentHandshake (pid : PeerId) : M Unit := do
  let now ← hiddenClock64 .resetLastSent
  setPeer pid { (← getPeer pid) with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

/-- wg_birthdate_has_expired (timers.h:25-29), with the recorded clock:
    `(s64)(birthday + seconds * NSEC_PER_SEC) <= (s64)now`, computed in
    `Int64` as the C computes it (review item 8). Returns the outcome and
    the two `s64` operands, which the built code records at the caller's
    line (never at timers.h:28: the inline is folded into its caller). -/
def birthdateTest (birthday : Int64) (seconds : Nat) : M (Bool × Int × Int) := do
  let now ← hiddenClock64 .birthdateExpired
  let lhs := birthday + seconds.toInt64 * NSEC_PER_SEC64
  return (lhs ≤ now, lhs.toInt, now.toInt)

/-- The age test where no comparison is declared (a cut's own read). -/
def birthdateHasExpired (birthday : Int64) (seconds : Nat) : M Bool := do
  return (← birthdateTest birthday seconds).1

/-- The age test as the declared comparison `d` (`Decision.comparison`:
    `lhs <= now`, both non-constant): the decision's outcome is `f expired`
    (`f` negates where the C does), the operands are the test's. -/
def branchExpired (d : Decision) (birthday : Int64) (seconds : Nat) (f : Bool → Bool := id) : M Bool := do
  let (expired, lhs, now) ← birthdateTest birthday seconds
  branchCmp d (f expired) lhs now

/-- `handshake_zero` (noise.c:78-86). -/
def handshakeZero (pid : PeerId) : M Unit := do
  let z : List UInt8 := List.replicate 32 0
  let p ← getPeer pid
  setPeer pid { p with ephemeralPrivate := z, remoteEphemeral := z, hash := z, chainingKey := z,
                       remoteIndex := 0, handshakeState := 0 }

/-- wg_peer_get_maybe_zero (peer.c:71-78): a strong reference, unless the
    peer is NULL or its count already reached zero. -/
def peerGetMaybeZero (peer : Option PeerId) : M (Option PeerId) := do
  -- `unlikely(!peer || !kref_get_unless_zero(&peer->refcount))`
  if ← branch .peerGetMaybeZeroNull peer.isNone then return none
  let some pid := peer | invariant "unreachable"
  requireNotPending pid "a reference count the handshake worker also changes"
  let p ← getPeer pid
  let live ← refcountIncNotZero p.refcount
  if ← branch .peerGetMaybeZeroDead !live then return none
  setPeer pid { p with refcount := p.refcount + 1 }
  return some pid

/-- wg_index_hashtable_lookup (peerlookup.c:201-226): the entry under
    `index` whose kind is in `kinds` (its owner, which the caller casts the
    entry to), with a strong reference to its peer (`*peer`). -/
def indexLookup (kinds : List IndexKind) (index : Nat) : M (Option (IndexOwner × PeerId)) := do
  let mut entry : Option IndexEntry := none
  let mut stopped := false
  for e in ← indexBucket index do
    _ ← branch .idxWalk true
    if ← branch .idxMatch (e.index == index) then
      if ← branch .idxTypeMatch (kinds.contains e.kind) then entry := some e
      stopped := true
      break
  if !stopped then _ ← branch .idxWalk false
  if ← branch .idxFound entry.isSome then
    let some e := entry | invariant "unreachable"
    -- `entry->peer = wg_peer_get_maybe_zero(entry->peer)` (peerlookup.c:218):
    -- the owner's peer word is read and the get's result stored back into
    -- it, so a failed get leaves NULL there, a later lookup of the same
    -- entry takes wg_peer_get_maybe_zero's `!peer` arm, and the owner's
    -- other reads of the word (`PACKET_PEER`, `entry.peer->device`) find
    -- NULL (found by the binary adequacy grind, 2026-10-14). The failed get
    -- is unreachable on one CPU without preemption
    -- (docs/2026-10-05-l-lifecycle.md 16.6); the data flow is the C's
    -- regardless.
    let peer ← peerGetMaybeZero (← e.owner.peerWord)
    e.owner.setPeerWord peer
    -- `if (likely(entry->peer)) *peer = entry->peer; else entry = NULL;`
    if ← branch .idxPeerAlive peer.isSome then
      let some pid := peer | invariant "unreachable"
      return some (e.owner, pid)
  return none

/-- `wg_pubkey_hashtable_lookup` (peerlookup.c:53-71): a map lookup (the
    random-keyed bucket walk is a cut point), then wg_peer_get_maybe_zero.
    Returns a strong reference. -/
def pubkeyLookup (key : Key) : M (Option PeerId) := do
  let found := ((← getDev).peerHashtable.find? (·.1 == key)).map (·.2)
  -- The bucket walk's `!memcmp` is reported once, with the walk's result:
  -- the misses before a match depend on the random bucket key.
  _ ← branch .pubkeyLookupMatch found.isSome
  peerGetMaybeZero found


/-- wg_noise_handshake_init (noise.c:59-76). -/
def handshakeInit (pid : PeerId) (presharedKey : Option Key) : M Unit := do
  -- `handshake->entry.type = INDEX_HASHTABLE_HANDSHAKE; handshake->entry.peer = peer`
  -- (noise.c:67-68): the embedded entry's peer word, the owner itself
  IndexOwner.setPeerWord (.handshake pid) (some pid)
  if ← branch .handshakeInitHasPsk presharedKey.isSome then
    let p ← getPeer pid
    setPeer pid { p with presharedKey := presharedKey.getD p.presharedKey }
  precomputeStaticStatic pid

/-- wg_peer_create (peer.c:21-69). -/
def peerCreate (publicKey : Key) (presharedKey : Option Key) : M (Except Int PeerId) := do
  let d ← getDev
  if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE then
    return .error (-ENOMEM)
  if ← branch .peerCreateNoMem !(← hiddenAlloc .kmemCacheZallocPeer) then return .error (-ENOMEM)
  -- `dst_cache_init` (alloc_percpu_gfp): retired as a choice
  -- (docs/2026-10-05-a-alloc.md 6.4). The percpu allocator allocates only
  -- when no chunk has room (percpu.c:1851-1855), a state-dependent count, so
  -- the site would be lax and unsteerable; the arm stays dead, named.
  if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
  let pid := d.nextPeer
  let internalId := (← get).peerCounter + 1   -- atomic64_inc_return(&peer_counter)
  modify fun k => { k with peerCounter := internalId }
  modifyDev fun d => { d with nextPeer := pid + 1 }
  -- wg_cookie_init (zeroed: no cookie, is_valid and have_sent_mac1 false),
  -- then wg_cookie_checker_precompute_peer_keys (cookie.c:61-67):
  -- BLAKE2s("cookie--" || remote static) and BLAKE2s("mac1----" || remote static)
  setPeer pid { remoteStatic := publicKey, presharedKey := List.replicate 32 0,
                precomputedStaticStatic := List.replicate 32 0, internalId,
                cookieDecryptionKey := blake2s 32 [] ("cookie--".toUTF8.toList ++ publicKey),
                cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ publicKey) }
  -- W9: `dst_cache_init` (peer.c:36) ends with `dst_cache_reset`, whose
  -- jiffies the kernel records (kind 306): before the noise handshake init
  -- and the last-sent reset (peer.c:55) in the C's order
  dstCacheReset pid
  handshakeInit pid presharedKey
  -- cookie init, timers, work items, queues, kref_init (refcount 1)
  resetLastSentHandshake pid   -- peer.c:55
  -- NAPI
  modifyDev fun d => { d with peerList := d.peerList ++ [pid],   -- list_add_tail
                              peerHashtable := (publicKey, pid) :: d.peerHashtable,
                              numPeers := d.numPeers + 1 }
  return .ok pid

/-- peer_make_dead (peer.c:80-92). -/
def peerMakeDead (pid : PeerId) : M Unit := do
  modifyDev fun d => { d with peerList := d.peerList.filter (· != pid) }   -- list_del_init
  removeByPeer pid
  -- wg_pubkey_hashtable_remove (peerlookup.c:44-50): `hlist_del_init_rcu`'s
  -- `if (!hlist_unhashed(n))` (rculist.h:183), the twin of the index remove's
  -- decision (the Peer audit's F4); the entry is absent either way
  _ ← branch .pubkeyRemoveHashed ((← getDev).peerHashtable.any (·.2 == pid))
  modifyDev fun d => { d with peerHashtable := d.peerHashtable.filter (·.2 != pid) }
  setPeer pid { (← getPeer pid) with isDead := true }

end Leanux.WG
