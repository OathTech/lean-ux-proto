import Leanux.WG.Netlink
import Leanux.WG.NoiseCrypto

/-!
# drivers/net/wireguard/noise.c — handshake messages, and the send worker

Both roles' messages are mirrored with every value (Curve25519, BLAKE2s, HMAC,
ChaCha20-Poly1305 references). The random ephemeral secrets, the clock read in
`tai64n_now` and the random indices are hidden inputs, recorded by the patched
kernel at their source and consumed here (`hidden`). Routing and the UDP send
below `wg_socket_send_skb_to_peer` are a cut point; a sent datagram is recorded
as an output in `World.sent`.

Time comes from the environment's timing contract (`World.timing`): the flood
test and the consumption-time update ask how long it has been since the last
consumed initiation, and the traversal timer asks whether it could expire
within the trace.
-/

namespace Leanux.WG
open Leanux

def HANDSHAKE_ZEROED : Nat := 0
def HANDSHAKE_CREATED_INITIATION : Nat := 1
def HANDSHAKE_CONSUMED_INITIATION : Nat := 2
def HANDSHAKE_CREATED_RESPONSE : Nat := 3
def HANDSHAKE_CONSUMED_RESPONSE : Nat := 4
def MESSAGE_HANDSHAKE_RESPONSE_LEN : Nat := 92
def INITIATIONS_PER_SECOND : Nat := 50
/-- `CONFIG_HZ` (kernel/config-x86_64-net-choice). -/
def HZ : Nat := 250

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
  let some (ckSs, key) := ss | invariant "unreachable"
  let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
  if ← branch .consumeTimestampFailed ts.isNone then return ← out peer none
  let some (t, hashT) := ts | invariant "unreachable"
  let p ← getPeer pid
  let replay := memcmp t p.latestTimestamp != .gt
  -- `(s64)last_initiation_consumption + NSEC_PER_SEC / INITIATIONS_PER_SECOND
  -- > (s64)ktime_get_coarse_boottime_ns()`, computed before the test
  let floodLhs := p.lastInitiationConsumption + NSEC_PER_SEC / INITIATIONS_PER_SECOND
  let now ← hiddenClock .floodNow
  if ← orM (branch .consumeReplay replay) (branchCmp .consumeFlood (floodLhs > now) floodLhs now) then
    return ← out peer none
  -- Success! Copy everything to peer
  setPeer pid { (← getPeer pid) with remoteEphemeral := e }
  if ← branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt) then
    setPeer pid { (← getPeer pid) with latestTimestamp := t }
  setPeer pid { (← getPeer pid) with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4 }
  -- `(s64)(last_initiation_consumption - (initiation_consumption = now)) < 0`
  let consumption ← hiddenClock .consumptionNow
  let last := (← getPeer pid).lastInitiationConsumption
  if ← branch .consumeLaterTime (last - consumption < 0) then
    setPeer pid { (← getPeer pid) with lastInitiationConsumption := consumption }
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
  out peer (some pid)

/-- `cpu_to_le32`. -/
def le32 (n : Nat) : List UInt8 := (List.range 4).map fun k => UInt8.ofNat (n / 256 ^ k % 256)

/-- tai64n_now (noise.c:496-514) from the recorded `struct timespec64`: the
    nanoseconds rounded down to a power of two (2^24, the largest below
    NSEC_PER_SEC / INITIATIONS_PER_SECOND), then TAI64N big-endian. -/
def tai64n (now : List UInt8) : List UInt8 :=
  let le (bs : List UInt8) := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
  let sec := le (now.take 8)
  let nsec := le ((now.drop 8).take 8)
  let be (n width : Nat) := (List.range width).reverse.map fun k => UInt8.ofNat (n / 256 ^ k % 256)
  be ((0x400000000000000a + sec) % 2 ^ 64) 8 ++ be (nsec - nsec % 2 ^ 24) 4

/-- The handshake state the C updates in place (`handshake->chaining_key`,
    `hash`). -/
private def setChain (pid : PeerId) (ck hash : List UInt8) : M Unit := do
  setPeer pid { (← getPeer pid) with chainingKey := ck, hash }

/-- wg_noise_handshake_create_initiation (noise.c:516-581): the message
    without its MACs, if created. The ephemeral secret, the clock read and the
    index are recorded hidden inputs. -/
def createInitiation (pid : PeerId) : M (Option (List UInt8)) := do
  let identity := (← getDev).staticIdentity
  if ← branch .initNoIdentity !identity.hasIdentity then return none
  let p ← getPeer pid
  -- handshake_init(chaining_key, hash, remote_static)
  let h := noiseHash (handshakeInitHash ++ p.remoteStatic)
  setChain pid handshakeInitChainingKey h
  -- e: curve25519_generate_secret: get_random_bytes_wait (recorded), then the clamp
  let secret := clamp (← hidden .initEphemeral)
  setPeer pid { (← getPeer pid) with ephemeralPrivate := secret }
  let (pub, ok) ← generatePublic secret
  if ← branch .initNoEphemeral !ok then return none
  let some e := pub | invariant "unreachable"
  let (ck, h) ← messageEphemeral false e handshakeInitChainingKey h
  setChain pid ck h
  -- es
  let es ← mixDh true ck secret p.remoteStatic
  if ← branch .initEsFailed es.isNone then return none
  let some (ck, key) := es | invariant "unreachable"
  -- s: message_encrypt
  let encStatic := aeadEncrypt key noiseNonce identity.staticPublic h
  let h := noiseHash (h ++ encStatic)
  setChain pid ck h
  -- ss
  let ss ← mixPrecomputedDh ck p.precomputedStaticStatic
  if ← branch .initSsFailed ss.isNone then return none
  let some (ck, key) := ss | invariant "unreachable"
  -- {t}
  let timestamp := tai64n (← hidden .tai64nNow)
  let encTime := aeadEncrypt key noiseNonce timestamp h
  let h := noiseHash (h ++ encTime)
  setChain pid ck h
  let index ← indexInsert pid .handshake
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CREATED_INITIATION }
  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)

/-- wg_noise_handshake_create_response (noise.c:667-725): the message without
    its MACs, if created. The ephemeral secret and the index are recorded
    hidden inputs. -/
def createResponse (pid : PeerId) : M (Option (List UInt8)) := do
  let p ← getPeer pid
  if ← branch .respNotConsumed (p.handshakeState != HANDSHAKE_CONSUMED_INITIATION) then return none
  let receiver := p.remoteIndex
  -- e
  let secret := clamp (← hidden .respEphemeral)   -- curve25519_generate_secret
  setPeer pid { (← getPeer pid) with ephemeralPrivate := secret }
  let (pub, ok) ← generatePublic secret
  if ← branch .respNoEphemeral !ok then return none
  let some e := pub | invariant "unreachable"
  let (ck, h) ← messageEphemeral false e p.chainingKey p.hash
  setChain pid ck h
  -- ee
  let ee ← mixDh false ck secret p.remoteEphemeral
  if ← branch .respEeFailed ee.isNone then return none
  let some (ck, _) := ee | invariant "unreachable"
  setChain pid ck h
  -- se
  let se ← mixDh false ck secret p.remoteStatic
  if ← branch .respSeFailed se.isNone then return none
  let some (ck, _) := se | invariant "unreachable"
  -- psk: mix_psk (kdf with three outputs, then mix_hash of the second)
  let outs ← kdf true true ck p.presharedKey
  let (ck, tempHash, key) := (outs.head!, outs.getD 1 [], outs.getD 2 [])
  let h := noiseHash (h ++ tempHash)
  -- {}
  let encNothing := aeadEncrypt key noiseNonce [] h
  let h := noiseHash (h ++ encNothing)
  setChain pid ck h
  let index ← indexInsert pid .handshake
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CREATED_RESPONSE }
  return some (le32 2 ++ le32 index ++ le32 receiver ++ e ++ encNothing ++ List.replicate 32 0)

/-- wg_cookie_add_mac_to_packet (cookie.c:157-180): MAC1 under the peer's
    key; no cookie was ever received, so MAC2 is zero. -/
def addMacToPacket (pid : PeerId) (msg : List UInt8) : M (List UInt8) := do
  let p ← getPeer pid
  let body := msg.take (msg.length - 32)
  let mac1 := blake2s 16 p.cookieMac1Key body   -- compute_mac1
  setPeer pid { p with lastMac1Sent := mac1, haveSentMac1 := true }
  -- `is_valid && !wg_birthdate_has_expired(...)`
  if ← andM (branch .addMacCookieValid false) (branch .addMacCookieFresh false) then unsupported "unreachable"
  return body ++ mac1 ++ List.replicate 16 0

/-- derive_keys (noise.c:392-402) into the new keypair: the birthdate (a
    recorded clock read), then `kdf(first, second, chaining_key)` with no
    input. The initiator's first output is its sending key, the responder's
    its receiving key (noise.c:834-839). -/
def deriveKeys (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) : M Unit := do
  let birthdate ← hiddenClock .deriveKeysBirthdate
  let outs ← kdf true false chainingKey []
  let sym (key : List UInt8) : SymmetricKey := { key, birthdate, isValid := true }
  let (first, second) := (sym (outs.getD 0 []), sym (outs.getD 1 []))
  let k ← getKeypair kp
  setKeypair kp (if initiator then { k with sending := first, receiving := second }
                 else { k with receiving := first, sending := second })

/-- wg_noise_handshake_begin_session (noise.c:816-861): after creating a
    response (the responder) or consuming one (the initiator). -/
def beginSession (pid : PeerId) : M Bool := do
  let st := (← getPeer pid).handshakeState
  if ← andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
      (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) then return false
  let created ← keypairCreate pid
  if ← branch .sessionNoKeypair created.isNone then return false
  let some kp := created | invariant "unreachable"
  let p ← getPeer pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  setKeypair kp { (← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex }
  if ← branch .sessionInitiator initiator then deriveKeys kp true p.chainingKey
  else deriveKeys kp false p.chainingKey
  handshakeZero pid
  if ← branch .sessionAlive !(← getPeer pid).isDead then
    addNewKeypair pid kp
    -- the keypair's entry takes the handshake's place
    if !(← indexReplaceHandshake pid kp) then invariant "the handshake has no index entry"
    return true
  unsupported "a dead peer finishing a session"

/-- wg_noise_handshake_consume_response (noise.c:727-814). Returns the peer,
    with a reference, on success. -/
def consumeResponse (msg : List UInt8) : M (Option PeerId) := do
  let identity := (← getDev).staticIdentity
  if ← branch .crespNoIdentity !identity.hasIdentity then return none
  -- `src->receiver_index`, of a handshake
  let entry ← indexLookup [.handshake] (u32le msg 8)
  if ← branch .crespNoHandshake entry.isNone then return none
  let some e := entry | invariant "unreachable"
  let pid := e.peer
  let fail : M (Option PeerId) := do
    peerPut (some pid)
    return none
  -- the copies taken under the read lock
  let p ← getPeer pid
  let state := p.handshakeState
  if ← branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION) then return ← fail
  -- e
  let eph := (msg.drop 12).take 32
  let (ck, h) ← messageEphemeral true eph p.chainingKey p.hash
  -- ee
  let ee ← mixDh false ck p.ephemeralPrivate eph
  if ← branch .crespEeFailed ee.isNone then return ← fail
  let some (ck, _) := ee | invariant "unreachable"
  -- se
  let se ← mixDh false ck identity.staticPrivate eph
  if ← branch .crespSeFailed se.isNone then return ← fail
  let some (ck, _) := se | invariant "unreachable"
  -- psk: mix_psk (kdf with three outputs, then mix_hash of the second)
  let outs ← kdf true true ck p.presharedKey
  let (ck, tempHash, key) := (outs.getD 0 [], outs.getD 1 [], outs.getD 2 [])
  let h := noiseHash (h ++ tempHash)
  -- {}
  let dec ← messageDecrypt ((msg.drop 44).take 16) key h
  if ← branch .crespDecryptFailed dec.isNone then return ← fail
  let some (_, h) := dec | invariant "unreachable"
  -- the state recheck under the write lock (one CPU: nothing ran meanwhile)
  if ← branch .crespStateChanged ((← getPeer pid).handshakeState != state) then return ← fail
  setPeer pid { (← getPeer pid) with remoteEphemeral := eph, hash := h, chainingKey := ck,
                                     remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE }
  return some pid

/-- mod_peer_timer (timers.c:30-39). -/
def modPeerTimer (pid : PeerId) : M Unit := do
  let running := (← getDev).running
  _ ← andM (branch .modTimerRunning running) (branch .modTimerAlive !(← getPeer pid).isDead)

/-- wg_timers_handshake_complete (timers.c:192-198): the retransmit timer's
    deletion and the attempt counters are timer state (cut); the wall clock
    (`ktime_get_real_ts64`, a recorded `struct timespec64`) becomes the
    dump's `last_handshake`. -/
def timersHandshakeComplete (pid : PeerId) : M Unit := do
  let now ← hidden .walltimeLastHandshake
  setPeer pid { (← getPeer pid) with walltimeLastHandshake := now }

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
    `World.sent`, and the environment delivers it. -/
def sendBufferToPeer (pid : PeerId) (bytes : List UInt8) : M Unit := do
  if ← branch .sendBufNoMem !(← envOk .allocSkb) then return   -- -ENOMEM
  let p ← getPeer pid
  let family := (p.endpoint.map (·.family)).getD 0
  let sent ← do
    if ← branch .sendSkbInet (family == AF_INET) then pure true
    else if ← branch .sendSkbInet6 (family == AF_INET6) then pure true
    else pure false   -- dev_kfree_skb; -EAFNOSUPPORT
  -- send4/send6 (a cut point) choose the IP ident; the loopback delivery
  -- runs NET_RX in a section nested in the worker's (D1 stream A)
  skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]
  if ← branch .sendSkbOk sent then
    let some e := p.endpoint | invariant "unreachable"
    setPeer pid { p with txBytes := p.txBytes + bytes.length }
    modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes }] }

/-- wg_timers_handshake_initiated (timers.c:182-187): the retransmit timer,
    with `get_random_u32_below(REKEY_TIMEOUT_JITTER_MAX_JIFFIES)` inline for
    the constant ceiling `HZ / 3` = 83 (random.h:76-80): `get_random_u8`
    draws (recorded) until `(u8)(83 * r) >= 256 % 83`. The jitter only sets
    the expiry, beyond the trace. -/
def timersHandshakeInitiated (pid : PeerId) : M Unit := do
  let ceil := HZ / 3   -- REKEY_TIMEOUT_JITTER_MAX_JIFFIES; at most 256: the u8 path
  for _ in [0:256] do
    let r := (← hidden .retransmitJitter)[0]!.toNat
    if (ceil * r) % 256 ≥ 256 % ceil then
      modPeerTimer pid
      return
  unsupported "256 rejected jitter draws"

/-- wg_packet_send_handshake_response (send.c:85-108). -/
def sendHandshakeResponse (pid : PeerId) : M Unit := do
  let now ← hiddenClock .respLastSent   -- last_sent_handshake = now
  setPeer pid { (← getPeer pid) with lastSentHandshake := now }
  let created ← createResponse pid
  if ← branch .respCreated created.isSome then
    let some msg := created | invariant "unreachable"
    let msg ← addMacToPacket pid msg
    if ← branch .respSessionBegun (← beginSession pid) then
      modPeerTimer pid   -- wg_timers_session_derived
      timersTraversal pid
      -- wg_timers_any_authenticated_packet_sent: del_timer
      let now ← hiddenClock .respLastSentAgain
      setPeer pid { (← getPeer pid) with lastSentHandshake := now }
      sendBufferToPeer pid msg

/-- wg_packet_send_handshake_initiation (send.c:21-44). -/
def sendHandshakeInitiation (pid : PeerId) : M Unit := do
  -- `!wg_birthdate_has_expired(last_sent_handshake, REKEY_TIMEOUT)`
  if ← branch .initRateLimited !(← birthdateHasExpired (← getPeer pid).lastSentHandshake REKEY_TIMEOUT) then return
  let now ← hiddenClock .initLastSent   -- last_sent_handshake = now
  setPeer pid { (← getPeer pid) with lastSentHandshake := now }
  let created ← createInitiation pid
  if ← branch .initCreated created.isSome then
    let some msg := created | invariant "unreachable"
    let msg ← addMacToPacket pid msg
    timersTraversal pid
    -- wg_timers_any_authenticated_packet_sent: del_timer
    let now ← hiddenClock .initLastSentAgain
    setPeer pid { (← getPeer pid) with lastSentHandshake := now }
    sendBufferToPeer pid msg
    timersHandshakeInitiated pid

/-- wg_packet_handshake_send_worker (send.c:46-53), run by the environment
    for a peer whose work is queued. -/
def handshakeSendWorker (pid : PeerId) : M Unit := do
  sendHandshakeInitiation pid
  peerPut (some pid)

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
