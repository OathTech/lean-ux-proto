import Leanux.WG.AllowedIps
import Leanux.Kernel.Refcount
import Leanux.WG.Blake2s

/-!
# drivers/net/wireguard/peer.c, peerlookup.c (public keys) and the noise.c
# static-identity functions on the configuration path

Cut points (no mirror state or decisions): `dst_cache_init`/`_reset`, timers,
work items, packet queues, NAPI add/enable/disable/del, `synchronize_net`,
`flush_workqueue`, the index hashtable, `call_rcu` freeing, the cookie keys
(BLAKE2s), and `endpoint_eq` (a pure equality predicate). The only keypair
is a responder's pending next keypair (`Leanux/WG/Handshake.lean`); nothing
else takes a reference to it, so putting it frees it.
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

/-- `hlist_del_init_rcu` of a peer's entry of this kind (a no-op if unhashed):
    wg_index_hashtable_remove (peerlookup.c:192-198). -/
def indexRemove (pid : PeerId) (kind : IndexKind) : M Unit :=
  modifyDev fun d => { d with indexTable := d.indexTable.filter fun e => !(e.peer == pid && e.kind == kind) }

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
    indexRemove pid .handshake
    -- wg_packet_purge_staged_packets: DEV_STATS_ADD(tx_dropped, qlen)
    modifyDev fun d => { d with txDropped := d.txDropped + p.staged, peers := d.peers.erase pid }

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
  -- precompute_key(message_mac1_key, static_public, "mac1----"); the cookie
  -- encryption key is not read on the modeled paths
  let key ← do
    if ← branch .cookieDeviceHasIdentity identity.hasIdentity then
      pure (blake2s 32 [] ("mac1----".toUTF8.toList ++ identity.staticPublic))
    else pure (List.replicate 32 0)
  modifyDev fun d => { d with mac1Key := key }

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

/-- Whether a peer's entry of this kind is hashed. -/
def indexHashed (pid : PeerId) (kind : IndexKind) : M Bool :=
  return (← getDev).indexTable.any fun e => e.peer == pid && e.kind == kind

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
def indexInsert (pid : PeerId) (kind : IndexKind) : M Nat := do
  indexRemove pid kind
  -- `goto search_unused_slot` draws again; nothing else inserts meanwhile
  -- (one CPU), so the locked walk agrees with the unlocked one
  for _ in [0:64] do
    let draw ← hidden .indexDraw
    let index := draw.foldr (fun b acc => acc * 256 + b.toNat) 0   -- __le32
    if ← bucketHas .idxInsWalk1 .idxInsCollide1 index then continue
    -- the locked walk's collision (stolen meanwhile, peerlookup.c:148) needs
    -- a concurrent insert
    if ← bucketHas .idxInsWalk2 .idxInsCollide2 index then unsupported "an index stolen during insertion"
    modifyDev fun d => { d with indexTable := { index, peer := pid, kind } :: d.indexTable }
    return index
  unsupported "64 colliding index draws"

/-- wg_index_hashtable_replace (peerlookup.c:166-190) of a peer's handshake
    entry by its new keypair's, in place. Whether the handshake entry was
    hashed. -/
def indexReplaceHandshake (pid : PeerId) : M Bool := do
  let hashed ← indexHashed pid .handshake
  if ← branch .idxReplaceUnhashed !hashed then return false
  modifyDev fun d => { d with indexTable := d.indexTable.map fun e =>
    if e.peer == pid && e.kind == .handshake then { e with kind := .keypair } else e }
  return true

/-- `handshake_zero` (noise.c:78-86). -/
def handshakeZero (pid : PeerId) : M Unit := do
  let z : List UInt8 := List.replicate 32 0
  let p ← getPeer pid
  setPeer pid { p with ephemeralPrivate := z, remoteEphemeral := z, hash := z, chainingKey := z,
                       remoteIndex := 0, handshakeState := 0 }

/-- wg_noise_keypair_put (noise.c:131-140) of a peer's next keypair, which
    only its slot references (no data packet ever took one): the put frees
    it, and `keypair_free_kref` removes its index entry. -/
def keypairPutLive (pid : PeerId) (unreferenceNow : Bool) : M Unit := do
  if ← branch .keypairPutNull false then return
  if ← branch .keypairPutUnreferenceNow unreferenceNow then indexRemove pid .keypair
  if ← branch .keypairKrefPutReleased (← refcountDecAndTest 1) then indexRemove pid .keypair

/-- wg_noise_expire_current_peer_keypairs (noise.c:179-196). `handshake_clear`
    zeroes ephemeral state that the configuration path never set. -/
def expireCurrentPeerKeypairs (pid : PeerId) : M Unit := do
  requireNotPending pid "clearing the handshake"
  -- wg_noise_handshake_clear: remove the entry, then handshake_zero
  indexRemove pid .handshake
  handshakeZero pid
  -- wg_noise_reset_last_sent_handshake
  setPeer pid { (← getPeer pid) with lastSentExpired := true }
  -- `keypair->sending.is_valid = false`: session keys are not tracked
  _ ← branch .expireNextKeypair (← getPeer pid).nextKeypair
  if ← branch .expireCurrentKeypair false then unsupported "current keypair present"

/-- wg_noise_keypairs_clear (noise.c:151-177). -/
def keypairsClear (pid : PeerId) : M Unit := do
  if (← getPeer pid).nextKeypair then
    setPeer pid { (← getPeer pid) with nextKeypair := false }
    keypairPutLive pid true
  else keypairPutNull   -- next_keypair
  keypairPutNull   -- previous_keypair
  keypairPutNull   -- current_keypair

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
    `index` whose kind is in `kinds`, with a strong reference to its peer. -/
def indexLookup (kinds : List IndexKind) (index : Nat) : M (Option IndexEntry) := do
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
    let peer ← peerGetMaybeZero (some e.peer)
    if ← branch .idxPeerAlive peer.isSome then return entry
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
  if ← branch .handshakeInitHasPsk presharedKey.isSome then
    let p ← getPeer pid
    setPeer pid { p with presharedKey := presharedKey.getD p.presharedKey }
  precomputeStaticStatic pid

/-- wg_peer_create (peer.c:21-69). -/
def peerCreate (publicKey : Key) (presharedKey : Option Key) : M (Except Int PeerId) := do
  let d ← getDev
  if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE then
    return .error (-ENOMEM)
  if ← branch .peerCreateNoMem !(← envOk .kmemCacheZallocPeer) then return .error (-ENOMEM)
  if ← branch .peerCreateDstCacheFail !(← envOk .dstCacheInit) then return .error (-ENOMEM)
  let pid := d.nextPeer
  let internalId := (← getK).peerCounter + 1   -- atomic64_inc_return(&peer_counter)
  modifyK fun k => { k with peerCounter := internalId }
  modifyDev fun d => { d with nextPeer := pid + 1 }
  -- wg_cookie_checker_precompute_peer_keys: BLAKE2s("mac1----" || remote static)
  setPeer pid { remoteStatic := publicKey, presharedKey := List.replicate 32 0,
                precomputedStaticStatic := List.replicate 32 0, internalId,
                cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ publicKey) }
  handshakeInit pid presharedKey
  -- cookie init, timers, work items, queues, kref_init (refcount 1), NAPI
  modifyDev fun d => { d with peerList := d.peerList ++ [pid],   -- list_add_tail
                              peerHashtable := (publicKey, pid) :: d.peerHashtable,
                              numPeers := d.numPeers + 1 }
  return .ok pid

/-- peer_make_dead (peer.c:80-92). -/
def peerMakeDead (pid : PeerId) : M Unit := do
  modifyDev fun d => { d with peerList := d.peerList.filter (· != pid) }   -- list_del_init
  removeByPeer pid
  modifyDev fun d => { d with peerHashtable := d.peerHashtable.filter (·.2 != pid) }
  setPeer pid { (← getPeer pid) with isDead := true }

/-- peer_remove_after_dead (peer.c:94-150). -/
def peerRemoveAfterDead (pid : PeerId) : M Unit := do
  if ← branch .peerRemoveNotDead !(← getPeer pid).isDead then
    unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)"
  keypairsClear pid
  -- timers stop; flush packet_crypt_wq twice; napi disable/del; flush handshake_send_wq
  if (← getDev).numPeers == 0 then invariant "--num_peers below zero"
  modifyDev fun d => { d with numPeers := d.numPeers - 1 }
  peerPut (some pid)

/-- wg_peer_remove (peer.c:156-165). -/
def peerRemove (peer : Option PeerId) : M Unit := do
  if ← branch .peerRemoveNull peer.isNone then return
  let some pid := peer | invariant "unreachable"
  -- flush_workqueue runs a queued worker inside this call: always a race here
  if (← getPeer pid).handshakePending then unsupported "removing a peer with queued handshake work"
  mayHaveSlept   -- synchronize_net(), flush_workqueue()
  peerMakeDead pid
  -- synchronize_net()
  peerRemoveAfterDead pid

/-- wg_peer_remove_all (peer.c:167-184). -/
def peerRemoveAll : M Unit := do
  free   -- wg_allowedips_free: avoid traversing each peer
  let dead := (← getDev).peerList
  for pid in dead do
    if (← getPeer pid).handshakePending then unsupported "removing a peer with queued handshake work"
  mayHaveSlept   -- synchronize_net(), flush_workqueue()
  for pid in dead do
    _ ← branch .peerRemoveAllIter1 true
    peerMakeDead pid   -- then list_add_tail(&peer->peer_list, &dead_peers)
  _ ← branch .peerRemoveAllIter1 false
  -- synchronize_net()
  for pid in dead do
    _ ← branch .peerRemoveAllIter2 true
    peerRemoveAfterDead pid
  _ ← branch .peerRemoveAllIter2 false

end Leanux.WG
