import Leanux.Proofs.WG.Progress.HandshakeFiniteSource
import Leanux.Proofs.WG.Index.CreatorSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG
/-- The original response creator, factoring only its two curve-bearing leaves. -/
def responseWith (generate : Key → WG.M (Option Key × Bool))
    (dh : Bool → Key → Key → Key → WG.M (Option (Key × Key)))
    (pid : PeerId) : WG.M (Option Key) := do
  let p ← getPeer pid
  if ← branch .respNotConsumed (p.handshakeState != HANDSHAKE_CONSUMED_INITIATION) then return none
  let receiver := p.remoteIndex
  -- e
  let secret := clamp (← hidden .respEphemeral)   -- curve25519_generate_secret
  setPeer pid { (← getPeer pid) with ephemeralPrivate := secret }
  let (pub, ok) ← generate secret
  if ← branch .respNoEphemeral !ok then return none
  let some e := pub | invariant "unreachable"
  let (ck, h) ← messageEphemeral false e p.chainingKey p.hash
  (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck h
  -- ee
  let ee ← dh false ck secret p.remoteEphemeral
  if ← branch .respEeFailed ee.isNone then return none
  let some (ck, _) := ee | invariant "unreachable"
  (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck h
  -- se
  let se ← dh false ck secret p.remoteStatic
  if ← branch .respSeFailed se.isNone then return none
  let some (ck, _) := se | invariant "unreachable"
  -- psk: mix_psk (kdf with three outputs, then mix_hash of the second)
  let outs ← kdf true true ck p.presharedKey
  let (ck, tempHash, key) := (← kdfOut outs 0, ← kdfOut outs 1, ← kdfOut outs 2)
  let h := noiseHash (h ++ tempHash)
  -- {}
  let encNothing := aeadEncrypt key noiseNonce [] h
  let h := noiseHash (h ++ encNothing)
  (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck h
  -- `wg_index_hashtable_insert(handshake->entry.peer->device->index_hashtable, ...)`
  -- (noise.c:713-715): the table through the entry's peer word
  _ ← IndexOwner.peerDeref (.handshake pid)
  let index ← indexInsert (.handshake pid)
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CREATED_RESPONSE }
  return some (le32 2 ++ le32 index ++ le32 receiver ++ e ++ encNothing ++ List.replicate 32 0)


theorem responseWith_source (pid : PeerId) :
    responseWith WG.generatePublic WG.mixDh pid = WG.createResponse pid := by
  unfold responseWith WG.createResponse
  rfl

/-- Complete response creation with finite curve inversion at each reached call. -/
def createResponse (pid : PeerId) : WG.M (Option Key) :=
  responseWith generatePublic mixDh pid

/-- Exact all-input source correspondence; refusals, writes and Stops retain
their original order. The index search still uses its actual finite budget. -/
theorem createResponse_source (pid : PeerId) :
    WG.createResponse pid = createResponse pid := by
  rw [← responseWith_source]
  unfold createResponse
  have generateEq : WG.generatePublic = generatePublic :=
    funext generatePublic_source
  have dhEq : WG.mixDh = mixDh :=
    funext fun key => funext fun chain => funext fun secret => funext fun point =>
      mixDh_source key chain secret point
  rw [generateEq, dhEq]

end Leanux.Proofs.WG.Progress.HandshakeFinite
