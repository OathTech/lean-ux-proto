import Leanux.WG.Peer

/-!
# drivers/net/wireguard/noise.c — the keypair store's references

`wg_noise_keypair_get` and `wg_noise_keypair_put` over the device's keypair
store (`Device.keypairs`), the D1 sprint's shared interface
(docs/2026-10-04-d1-sprint.md); keypair creation and rotation
(`keypair_create`, `add_new_keypair`); clearing and expiring a peer's
keypairs; and peer removal (peer.c), which clears them.
-/

namespace Leanux.WG
open Leanux

/-- wg_noise_keypair_get (noise.c:142-149): a reference, unless the keypair
    is NULL or its count already reached zero. -/
def keypairGet (kp : Option KeypairId) : M (Option KeypairId) := do
  -- `unlikely(!keypair || !kref_get_unless_zero(&keypair->refcount))`
  if ← branch .keypairGetNull kp.isNone then return none
  let some id := kp | invariant "unreachable"
  let k ← getKeypair id
  if ← branch .keypairGetZero !(← refcountIncNotZero k.refcount) then return none
  setKeypair id { k with refcount := k.refcount + 1 }
  return some id

/-- wg_noise_keypair_put (noise.c:131-140) through the store: the index
    entry is removed when `unreference_now`, and the last reference's release
    (`keypair_free_kref`) removes it again and frees the keypair (`call_rcu`,
    a cut point). Both removals find the table through the entry's peer word
    (`keypair->entry.peer->device->index_hashtable`, noise.c:126, :137). -/
def keypairPut (kp : Option KeypairId) (unreferenceNow : Bool) : M Unit := do
  if ← branch .keypairPutNull kp.isNone then return
  let some id := kp | invariant "unreachable"
  let k ← getKeypair id
  let removeEntry : M Unit := do
    _ ← IndexOwner.peerDeref (.keypair id)
    indexRemove (.keypair id)
  if ← branch .keypairPutUnreferenceNow unreferenceNow then removeEntry
  setKeypair id { k with refcount := k.refcount - 1 }
  if ← branch .keypairKrefPutReleased (← refcountDecAndTest k.refcount) then
    removeEntry
    modifyDev fun d => { d with keypairs := d.keypairs.erase id }

/-- `p->keypairs`'s slots, updated in place. -/
private def modifyPeer (pid : PeerId) (f : Peer → Peer) : M Unit := do
  setPeer pid (f (← getPeer pid))

/-- keypair_create (noise.c:98-110): a zeroed keypair in the store, with the
    next `keypair_counter` value, the caller's peer word (`entry.peer`,
    noise.c:107: `handshake->entry.peer` as it is, :827) and one reference. -/
def keypairCreate (peer : Option PeerId) : M (Option KeypairId) := do
  -- kzalloc in a kworker: GFP_KERNEL, record-only (class b-kworker, Q2)
  let ok ← hiddenAlloc .kzallocKeypair
  if ← branch .keypairCreateNoMem !ok then return none
  let internalId := (← getK).keypairCounter + 1   -- atomic64_inc_return(&keypair_counter)
  modifyK fun k => { k with keypairCounter := internalId }
  let id := (← getDev).nextKeypairId
  modifyDev fun d => { d with nextKeypairId := id + 1 }
  setKeypair id { internalId, peer }   -- entry.type = KEYPAIR; entry.peer = peer; kref_init
  return some id

/-- add_new_keypair (noise.c:198-251). -/
def addNewKeypair (pid : PeerId) (newKeypair : KeypairId) : M Unit := do
  let p ← getPeer pid
  let (previous, next, current) := (p.keypairPrevious, p.keypairNext, p.keypairCurrent)
  if ← branch .addKeypairInitiator (← getKeypair newKeypair).iAmTheInitiator then
    if ← branch .addKeypairHasNext next.isSome then
      -- demote the pending next keypair to previous, and free the current
      modifyPeer pid fun p => { p with keypairNext := none, keypairPrevious := next }
      keypairPut current true
    else
      modifyPeer pid fun p => { p with keypairPrevious := current }
    keypairPut previous true
    modifyPeer pid fun p => { p with keypairCurrent := some newKeypair }
  else
    modifyPeer pid fun p => { p with keypairNext := some newKeypair }
    keypairPut next true
    modifyPeer pid fun p => { p with keypairPrevious := none }
    keypairPut previous true

/-- wg_noise_received_with_keypair (noise.c:253-291): the responder's key
    confirmation. A packet received under the `next` keypair slides it into
    `current`, the current into `previous`, and puts the old previous. The
    recheck under `keypair_update_lock` sees the same `next` on this one-CPU
    kernel (nothing else runs between the two reads in a softirq). -/
def receivedWithKeypair (pid : PeerId) (received : KeypairId) : M Bool := do
  -- `key_is_new = received_keypair == rcu_access_pointer(keypairs->next_keypair)`
  if ← branch .receivedNotNew ((← getPeer pid).keypairNext != some received) then return false
  -- spin_lock_bh(&keypairs->keypair_update_lock), then the double check
  if ← branch .receivedChanged ((← getPeer pid).keypairNext != some received) then return false
  let p ← getPeer pid
  let old := p.keypairPrevious
  modifyPeer pid fun p => { p with keypairPrevious := p.keypairCurrent }
  keypairPut old true
  modifyPeer pid fun p => { p with keypairCurrent := some received, keypairNext := none }
  return true

/-- wg_noise_keypairs_clear (noise.c:151-177): next, then previous, then
    current. -/
def keypairsClear (pid : PeerId) : M Unit := do
  let old := (← getPeer pid).keypairNext
  modifyPeer pid fun p => { p with keypairNext := none }
  keypairPut old true
  let old := (← getPeer pid).keypairPrevious
  modifyPeer pid fun p => { p with keypairPrevious := none }
  keypairPut old true
  let old := (← getPeer pid).keypairCurrent
  modifyPeer pid fun p => { p with keypairCurrent := none }
  keypairPut old true

/-- wg_noise_handshake_clear (noise.c:88-96): the handshake's index entry
    removed from the table its peer word names
    (`handshake->entry.peer->device->index_hashtable`, :92), then
    `handshake_zero`. -/
def handshakeClear (pid : PeerId) : M Unit := do
  _ ← IndexOwner.peerDeref (.handshake pid)
  indexRemove (.handshake pid)
  handshakeZero pid

/-- wg_noise_expire_current_peer_keypairs (noise.c:179-196). -/
def expireCurrentPeerKeypairs (pid : PeerId) : M Unit := do
  requireNotPending pid "clearing the handshake"
  handshakeClear pid
  resetLastSentHandshake pid
  let invalidate (kp : KeypairId) : M Unit := do
    let k ← getKeypair kp
    setKeypair kp { k with sending := { k.sending with isValid := false } }
  let p ← getPeer pid
  if ← branch .expireNextKeypair p.keypairNext.isSome then
    let some kp := p.keypairNext | invariant "unreachable"
    invalidate kp
  if ← branch .expireCurrentKeypair p.keypairCurrent.isSome then
    let some kp := p.keypairCurrent | invariant "unreachable"
    invalidate kp

/-- wg_queued_expired_zero_key_material (timers.c:122-133), the work item
    `clear_peer_work` on `handshake_send_wq`, queued by the zero-key timer
    (`Timers.lean`) with a peer reference, which it drops. -/
def queuedExpiredZeroKeyMaterial (pid : PeerId) : M Unit := do
  handshakeClear pid
  keypairsClear pid
  peerPut (some pid)

end Leanux.WG
