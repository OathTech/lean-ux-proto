import Leanux.WG.Netlink
import Leanux.WG.NoiseCrypto

/-!
# drivers/net/wireguard/noise.c — the responder side of the handshake

`wg_noise_handshake_consume_initiation` is mirrored with every value: the
chaining key, hash, DH results, decryptions and the timestamp all follow from
the message and the device's keys (Curve25519, BLAKE2s, HMAC, ChaCha20-Poly1305
references). `wg_noise_handshake_create_response` and
`wg_noise_handshake_begin_session` draw a random ephemeral key, so the
response's contents and the session keys are random; their decisions are
determined and mirrored, and the values that depend on randomness are not
tracked. The index hashtable (`wg_index_hashtable_insert/replace`, a random
index) and `wg_socket_send_buffer_to_peer` (routing, `send4`/`send6`) are cut
points; a sent datagram is recorded as an output in `World.sent`.

Time comes from the environment's timing contract (`World.timing`): the flood
test and the consumption-time update ask how long it has been since the last
consumed initiation, and the traversal timer asks whether it could expire
within the trace.
-/

namespace Leanux.WG
open Leanux

def HANDSHAKE_ZEROED : Nat := 0
def HANDSHAKE_CONSUMED_INITIATION : Nat := 2
def HANDSHAKE_CREATED_RESPONSE : Nat := 3
def HANDSHAKE_CONSUMED_RESPONSE : Nat := 4
def MESSAGE_HANDSHAKE_RESPONSE_LEN : Nat := 92
def INITIATIONS_PER_SECOND : Nat := 50

private def zeroKey : List UInt8 := List.replicate 32 0

/-- The little-endian 32-bit word at `off`. -/
def u32le (msg : List UInt8) (off : Nat) : Nat :=
  ((msg.drop off).take 4).foldr (fun b acc => acc * 256 + b.toNat) 0

/-- `memcmp(a, b, n)`'s sign, as a comparison of byte strings. -/
def memcmp : List UInt8 → List UInt8 → Ordering
  | a :: as, b :: bs => if a < b then .lt else if a > b then .gt else memcmp as bs
  | _, _ => .eq

/-- kdf (noise.c:344-390): the outputs it writes, and its decisions. `second`
    and `third` say whether the caller passes those destinations. -/
def kdf (second third : Bool) (chainingKey data : List UInt8) : M (List (List UInt8)) := do
  let outs := kdfOutputs chainingKey data (if third then 3 else if second then 2 else 1)
  -- `!first_dst || !first_len`: every caller passes the first
  if ← orM (branch .kdfNoFirstDst false) (branch .kdfNoFirstLen false) then return []
  if ← orM (branch .kdfNoSecondDst !second) (branch .kdfNoSecondLen false) then return outs.take 1
  if ← orM (branch .kdfNoThirdDst !third) (branch .kdfNoThirdLen false) then return outs.take 2
  return outs

/-- message_ephemeral (noise.c:485-495). -/
def messageEphemeral (copy : Bool) (e chainingKey hash : List UInt8) : M (List UInt8 × List UInt8) := do
  _ ← branch .msgEphemeralCopy copy
  let hash := noiseHash (hash ++ e)
  let outs ← kdf false false chainingKey e
  return (outs.head!, hash)

/-- mix_dh (noise.c:404-417): the new chaining key and key, unless the DH
    result is the null point. -/
def mixDh (key : Bool) (chainingKey priv pub : List UInt8) : M (Option (List UInt8 × List UInt8)) := do
  let (dh, nonNull) := curve25519 priv pub
  if ← branch .mixDhNull !nonNull then return none
  let outs ← kdf key false chainingKey dh
  return some (outs.head!, outs.getD 1 [])

/-- mix_precomputed_dh (noise.c:419-430). -/
def mixPrecomputedDh (chainingKey precomputed : List UInt8) : M (Option (List UInt8 × List UInt8)) := do
  if ← branch .mixPrecomputedNull (precomputed == zeroKey) then return none
  let outs ← kdf true false chainingKey precomputed
  return some (outs.head!, outs.getD 1 [])

/-- message_decrypt (noise.c:473-483): the plaintext and the new hash. -/
def messageDecrypt (sealed key hash : List UInt8) : M (Option (List UInt8 × List UInt8)) := do
  let plain := aeadDecrypt key noiseNonce sealed hash
  if ← branch .msgDecryptFailed plain.isNone then return none
  let some p := plain | invariant "unreachable"
  return some (p, noiseHash (hash ++ sealed))

/-- wg_noise_handshake_consume_initiation (noise.c:583-665). Returns the
    peer, with a reference, on success. -/
def consumeInitiation (msg : List UInt8) : M (Option PeerId) := do
  let out (peer : Option PeerId) (ret : Option PeerId) : M (Option PeerId) := do
    if ← branch .consumeFailedPut ret.isNone then peerPut peer
    return ret
  let identity := (← getDev).staticIdentity
  if ← branch .consumeNoIdentity !identity.hasIdentity then return ← out none none
  -- handshake_init: the precomputed initial chaining key and hash
  let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
  let e := (msg.drop 8).take 32
  let (ck, hash) ← messageEphemeral true e handshakeInitChainingKey hash
  let es ← mixDh true ck identity.staticPrivate e
  if ← branch .consumeEsFailed es.isNone then return ← out none none
  let some (ck, key) := es | invariant "unreachable"
  let st ← messageDecrypt ((msg.drop 40).take 48) key hash
  if ← branch .consumeStaticFailed st.isNone then return ← out none none
  let some (s, hash) := st | invariant "unreachable"
  let peer ← pubkeyLookup s
  if ← branch .consumeNoPeer peer.isNone then return ← out none none
  let some pid := peer | invariant "unreachable"
  let ss ← mixPrecomputedDh ck (← getPeer pid).precomputedStaticStatic
  if ← branch .consumeSsFailed ss.isNone then return ← out peer none
  let some (_, key) := ss | invariant "unreachable"
  let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
  if ← branch .consumeTimestampFailed ts.isNone then return ← out peer none
  let some (t, _) := ts | invariant "unreachable"
  let p ← getPeer pid
  let replay := memcmp t p.latestTimestamp != .gt
  -- `last_initiation_consumption + NSEC_PER_SEC / INITIATIONS_PER_SECOND > now`
  let flood := !((← get).timing.sinceLastConsumption (1000000000 / INITIATIONS_PER_SECOND))
  if ← orM (branch .consumeReplay replay) (branch .consumeFlood flood) then return ← out peer none
  -- success: remote_ephemeral, hash and chaining key are copied (not tracked)
  if ← branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt) then
    setPeer pid { (← getPeer pid) with latestTimestamp := t }
  setPeer pid { (← getPeer pid) with remoteIndex := u32le msg 4 }
  -- `(s64)(last_initiation_consumption - now) < 0`: then it becomes now
  _ ← branch .consumeLaterTime ((← get).timing.sinceLastConsumption 1)
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
  out peer (some pid)

/-- wg_noise_handshake_create_response (noise.c:667-725). The ephemeral key is
    random, so the values computed from it are not tracked; its decisions are
    determined. -/
def createResponse (pid : PeerId) : M Bool := do
  let p ← getPeer pid
  if ← branch .respNotConsumed (p.handshakeState != HANDSHAKE_CONSUMED_INITIATION) then return false
  -- curve25519_generate_public of a fresh clamped secret: never the null point
  _ ← branch .genPublicNullSecret false
  if ← branch .respNoEphemeral false then return false
  -- message_ephemeral in place, mix_dh(ee), mix_dh(se): their values are random
  _ ← branch .msgEphemeralCopy false
  _ ← kdf false false [] []
  -- ee: null iff the initiator's ephemeral is low-order, which es already rejected
  _ ← branch .mixDhNull false
  _ ← kdf false false [] []
  if ← branch .respEeFailed false then return false
  -- se: null iff the peer's static key is low-order, which ss already rejected
  _ ← branch .mixDhNull false
  _ ← kdf false false [] []
  if ← branch .respSeFailed false then return false
  _ ← kdf true true [] []   -- mix_psk
  -- message_encrypt; wg_index_hashtable_insert (a random index)
  setPeer pid { (← getPeer pid) with indexed := true, handshakeState := HANDSHAKE_CREATED_RESPONSE }
  return true

/-- add_new_keypair (noise.c:198-219) for the responder. -/
def addNewKeypair (pid : PeerId) : M Unit := do
  if ← branch .addKeypairInitiator false then unsupported "unreachable"
  -- next_keypair = new; wg_noise_keypair_put(old next); previous = NULL; put(old previous)
  if (← getPeer pid).nextKeypair then keypairPutLive true else keypairPutNull   -- old next_keypair
  keypairPutNull   -- the responder never has a previous keypair
  setPeer pid { (← getPeer pid) with nextKeypair := true }

/-- wg_noise_handshake_begin_session (noise.c:816-860) after creating a
    response. -/
def beginSession (pid : PeerId) : M Bool := do
  let st := (← getPeer pid).handshakeState
  if ← andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
      (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) then return false
  -- keypair_create (noise.c:98-110)
  let ok ← envOk .kzallocKeypair
  if ← branch .keypairCreateNoMem !ok then pure ()
  if ← branch .sessionNoKeypair !ok then return false
  if ← branch .sessionInitiator (st == HANDSHAKE_CONSUMED_RESPONSE) then unsupported "unreachable"
  _ ← kdf true false [] []   -- derive_keys: random session keys
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_ZEROED, remoteIndex := 0 }   -- handshake_zero
  if ← branch .sessionAlive !(← getPeer pid).isDead then
    addNewKeypair pid
    -- wg_index_hashtable_replace (peerlookup.c:166-190): create_response
    -- hashed the handshake's entry, and the keypair's takes its place
    if ← branch .idxReplaceUnhashed !(← getPeer pid).indexed then invariant "the handshake has no index entry"
    setPeer pid { (← getPeer pid) with indexed := false }
    return true
  unsupported "a dead peer finishing a session"

/-- mod_peer_timer (timers.c:30-39). -/
def modPeerTimer (pid : PeerId) : M Unit := do
  let running := (← getDev).running
  _ ← andM (branch .modTimerRunning running) (branch .modTimerAlive !(← getPeer pid).isDead)

/-- wg_timers_any_authenticated_packet_traversal (timers.c:212-217). A
    persistent keepalive timer that could expire within the trace is outside
    the domain (its expiry is not modeled). -/
def timersTraversal (pid : PeerId) : M Unit := do
  let interval := (← getPeer pid).persistentKeepaliveInterval
  if ← branch .traversalKeepalive (interval != 0) then
    if (← get).timing.timerMayExpire interval then unsupported "a persistent keepalive timer firing within the trace"
    modPeerTimer pid

/-- wg_socket_send_buffer_to_peer (socket.c:189-200) and
    wg_socket_send_skb_to_peer (socket.c:167-187). `send4`/`send6` (routing,
    the UDP tunnel transmit) are a cut point: the datagram is recorded in
    `World.sent`, and the environment checks it reaches a fixture socket. -/
def sendBufferToPeer (pid : PeerId) (len type receiver : Nat) : M Unit := do
  if ← branch .sendBufNoMem !(← envOk .allocSkb) then return   -- -ENOMEM
  let p ← getPeer pid
  let family := (p.endpoint.map (·.family)).getD 0
  let sent ← do
    if ← branch .sendSkbInet (family == AF_INET) then pure true
    else if ← branch .sendSkbInet6 (family == AF_INET6) then pure true
    else pure false   -- dev_kfree_skb; -EAFNOSUPPORT
  if ← branch .sendSkbOk sent then
    let some e := p.endpoint | invariant "unreachable"
    setPeer pid { p with txBytes := p.txBytes + len }
    modify fun w => { w with sent := w.sent ++ [(e.family, e.addr, e.port, len, type, receiver)] }

/-- wg_packet_send_handshake_response (send.c:85-108). -/
def sendHandshakeResponse (pid : PeerId) : M Unit := do
  setPeer pid { (← getPeer pid) with lastSentExpired := false }   -- last_sent_handshake = now
  -- create_response copies remote_index into the packet before begin_session zeroes it
  let receiver := (← getPeer pid).remoteIndex
  if ← branch .respCreated (← createResponse pid) then
    -- wg_cookie_add_mac_to_packet: no cookie was ever received
    if ← andM (branch .addMacCookieValid false) (branch .addMacCookieFresh false) then unsupported "unreachable"
    if ← branch .respSessionBegun (← beginSession pid) then
      modPeerTimer pid   -- wg_timers_session_derived
      timersTraversal pid
      -- wg_timers_any_authenticated_packet_sent: del_timer
      sendBufferToPeer pid MESSAGE_HANDSHAKE_RESPONSE_LEN 2 receiver

/-- wg_socket_set_peer_endpoint_from_skb (socket.c:299-306) with
    wg_socket_endpoint_from_skb (socket.c:235-256). -/
def setPeerEndpointFromSkb (pid : PeerId) (src : SkbSource) : M Unit := do
  let endpoint ← do
    if ← branch .epFromSkbInet (src.family == 4) then
      pure ({ family := AF_INET, addr := src.saddr, port := src.sport, src := src.daddr, srcIf := src.iif } : Endpoint)
    else if ← branch .epFromSkbInet6 (src.family == 6) then
      -- ipv6_iface_scope_id: nonzero only for link-local and scoped multicast
      if src.saddr / 2 ^ 118 == 0x3fa || src.saddr / 2 ^ 120 == 0xff then
        unsupported "a scoped IPv6 source address"
      pure ({ family := AF_INET6, addr := src.saddr, port := src.sport, src := src.daddr } : Endpoint)
    else invariant "an skb that is neither IPv4 nor IPv6"
  if ← branch .epFromSkbOk true then setPeerEndpoint pid endpoint

end Leanux.WG
