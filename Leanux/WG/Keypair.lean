import Leanux.WG.Peer

/-!
# drivers/net/wireguard/noise.c — the keypair store's references

`wg_noise_keypair_get` and `wg_noise_keypair_put` over the device's keypair
store (`Device.keypairs`). These are the D1 sprint's shared interface
(docs/2026-10-04-d1-sprint.md): the initiator stream builds keypair creation
and rotation on them, the data-path stream takes and drops references with
them.
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
    a cut point). -/
def keypairPut (kp : Option KeypairId) (unreferenceNow : Bool) : M Unit := do
  if ← branch .keypairPutNull kp.isNone then return
  let some id := kp | invariant "unreachable"
  let k ← getKeypair id
  let removeEntry : M Unit := modifyDev fun d =>
    { d with indexTable := d.indexTable.filter fun e => e.keypair != some id }
  if ← branch .keypairPutUnreferenceNow unreferenceNow then removeEntry
  setKeypair id { k with refcount := k.refcount - 1 }
  if ← branch .keypairKrefPutReleased (← refcountDecAndTest k.refcount) then
    removeEntry
    modifyDev fun d => { d with keypairs := d.keypairs.erase id }

end Leanux.WG
