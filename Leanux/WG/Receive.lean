import Leanux.WG.Handshake
import Leanux.WG.PrevQueue
import Leanux.WG.PtrRing

/-!
# drivers/net/wireguard/receive.c — the receive path and the handshake worker

The fixture's sender delivers one UDP datagram to wg0's socket over loopback,
so the IP and UDP headers are well formed: `prepare_skb_header`'s header
checks hold, and only the WireGuard message itself varies. The handshake
worker's coverage reaches the trace through remote KCOV (the U2 kernel). Cut
points:
`ip_tunnel_parse_protocol`, `pskb_may_pull`/`pskb_trim` (the datagram is
linear and in bounds), the ptr ring, `queue_work_on`, `dev_kfree_skb`.

Queued handshake messages wait in the device's `handshakeQueue`; the
environment (`Leanux/Env.lean`) runs `handshakeReceiveWorker` when the queued
work runs, before the operation ends. A handshake initiation with a valid
MAC1 enters Noise as the responder, and a handshake response with a valid
MAC1 completes wg0's own initiation (`Leanux/WG/Handshake.lean`), which then
sends its staged packets or a keepalive (`Leanux/WG/Send.lean`). Index lookups walk the
mirrored index hashtable, whose random indices are recorded hidden inputs. A cookie
reply for a known index is decrypted and stored (`cookieMessageConsume`). A data message for a keypair goes
to the decrypt queue and the peer's `rx_queue`; the decrypt worker and the
NAPI poll are in `Leanux/WG/RxData.lean` (D2).
-/

namespace Leanux.WG
open Leanux

def MESSAGE_HANDSHAKE_INITIATION : Nat := 1
def MESSAGE_HANDSHAKE_RESPONSE : Nat := 2
def MESSAGE_HANDSHAKE_COOKIE : Nat := 3
def MESSAGE_DATA : Nat := 4
def MESSAGE_MINIMUM_LENGTH : Nat := 32

/-- `SKB_TYPE_LE32`: the first little-endian 32-bit word (type and reserved
    bytes). -/
def messageType (msg : List UInt8) : Nat :=
  (msg.take 4).foldr (fun b acc => acc * 256 + b.toNat) 0

/-- validate_header_len (receive.c:28-45). GCC hoists the length tests to line
    30 and skips type tests it can already decide, so these are not declared
    comparisons. -/
def validateHeaderLen (msg : List UInt8) : M Nat := do
  let len := msg.length
  if ← branch .hdrTooShort (len < 4) then return 0
  let t := messageType msg
  if ← andM (branch .hdrData (t == MESSAGE_DATA))
      (branch .hdrDataLen (len ≥ MESSAGE_MINIMUM_LENGTH)) then
    return 16         -- sizeof(struct message_data)
  if ← andM (branch .hdrInit (t == MESSAGE_HANDSHAKE_INITIATION))
      (branch .hdrInitLen (len == 148)) then
    return 148
  if ← andM (branch .hdrResp (t == MESSAGE_HANDSHAKE_RESPONSE))
      (branch .hdrRespLen (len == 92)) then
    return 92
  if ← andM (branch .hdrCookie (t == MESSAGE_HANDSHAKE_COOKIE))
      (branch .hdrCookieLen (len == 64)) then
    return 64
  return 0

/-- prepare_skb_header (receive.c:47-90) for a well-formed loopback datagram. -/
def prepareSkbHeader (msg : List UInt8) : M Bool := do
  -- `!wg_check_packet_protocol(skb) || transport < head || transport + 8 > tail`
  let ok ← andM (branch .checkProtoParsed true) (branch .checkProtoMatches true)
  if ← orM (branch .prepBadProtocol !ok) (orM (branch .prepTransportBelowHead false)
      (branch .prepTransportBeyondTail false)) then return false
  if ← orM (branch .prepOffsetTooBig false) (branch .prepOffsetBeyondLen false) then return false
  if ← orM (branch .prepUdpLenSmall false) (branch .prepUdpLenLying false) then return false
  -- pskb_may_pull(skb, data_offset + sizeof(struct message_header)): the
  -- payload must hold the 4-byte header
  if ← orM (branch .prepPullFailed (msg.length < 4)) (branch .prepTrimFailed false) then return false
  if ← branch .prepLenMismatch false then return false
  let headerLen ← validateHeaderLen msg
  if ← branch .prepNoHeaderLen (headerLen == 0) then return false
  if ← branch .prepPullHeaderFailed false then return false
  return true

/-- wg_cookie_message_consume (cookie.c:198-236). The lookup takes a
    reference to the peer, which `out:` drops. -/
def cookieMessageConsume (msg : List UInt8) : M Unit := do
  -- `src->receiver_index`, of a handshake or a keypair
  let entry ← indexLookup [.handshake, .keypair] (u32le msg 4)
  if ← branch .cookieLookupMiss entry.isNone then return
  let some (_, pid) := entry | invariant "unreachable"   -- `peer`, the lookup's reference (peerlookup.c:220)
  let p ← getPeer pid
  if ← branch .cookieNoMac1Sent !p.haveSentMac1 then
    peerPut (some pid)   -- goto out
    return
  -- xchacha20poly1305_decrypt(cookie, encrypted_cookie, 32, last_mac1_sent,
  -- COOKIE_LEN, nonce, cookie_decryption_key)
  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent
  if ← branch .cookieDecryptOk cookie.isSome then
    let some c := cookie | invariant "unreachable"
    let birthdate ← hiddenClock64 .cookieBirthdate
    setPeer pid { (← getPeer pid) with cookie := c, cookieBirthdate := birthdate, cookieIsValid := true,
                                       haveSentMac1 := false }
  peerPut (some pid)   -- out:

/-- `cookie_mac_state` (cookie.h:14-19). -/
inductive MacState where
  | invalid | noCookie | withCookie | ratelimited
  deriving Repr, BEq

/-- `n` as `width` network-order (big-endian) bytes. -/
def netBytes (n width : Nat) : List UInt8 :=
  (List.range width).reverse.map fun k => UInt8.ofNat (n / 256 ^ k % 256)

/-- `COOKIE_SECRET_MAX_AGE` (cookie.h / messages.h): 120 s. -/
def COOKIE_SECRET_MAX_AGE : Nat := 120

/-- make_cookie (cookie.c:91-117): the secret rotated when older than
    `COOKIE_SECRET_MAX_AGE` (:96-102: the age test's clock read, declared
    as the comparison at the caller's line as review item 8 did for its
    siblings; the new birthdate's read at :99 and the 32 random bytes at
    :100 are records, consumed here), then `blake2s_128(key = secret,
    src_ip ‖ src_port)` with the source address by `skb->protocol`
    (:107-112, two decisions). The rotation is reachable only after a
    `wg_advance` of the age (`e_underload_cookie_rotated`); the function is
    listed in kcov.json since the receive correspondence audit (F7, F4). -/
def makeCookie (src : SkbSource) : M (List UInt8) := do
  -- `if (wg_birthdate_has_expired(checker->secret_birthdate, COOKIE_SECRET_MAX_AGE))`
  if ← branchExpired .cookieSecretExpired (← getDev).cookieSecretBirthdate COOKIE_SECRET_MAX_AGE then
    -- down_write; `secret_birthdate = ktime_get_coarse_boottime_ns()`;
    -- `get_random_bytes(checker->secret, NOISE_HASH_LEN)`; up_write
    let birthdate ← hiddenClock64 .cookieSecretRotateNow
    let secret ← hidden .cookieSecretRotated
    modifyDev fun d => { d with cookieSecretBirthdate := birthdate, cookieSecret := secret }
  let secret := (← getDev).cookieSecret
  let addr ← do
    if ← branch .cookieProtoIp (src.family == 4) then pure (netBytes src.saddr 4)
    else if ← branch .cookieProtoIpv6 (src.family == 6) then pure (netBytes src.saddr 16)
    else pure []   -- neither branch: the port alone (the skb came from one of the two UDP sockets)
  return blake2s 16 secret (addr ++ netBytes src.sport 2)

/-- Ratelimiter constants (ratelimiter.c:34-39): `NSEC_PER_SEC / 20`, times 5. -/
def PACKET_COST : Int := 1000000000 / 20
def TOKEN_MAX : Int := PACKET_COST * 5
/-- `max_entries` on the 256 MiB VM (docs/2026-10-05-e-dos.md §2.6:
    `roundup_pow_of_two((65536<<12)/(1<<14)/8) = 2048`, `* 8`). -/
def RL_MAX_ENTRIES : Nat := 16384

/-- wg_ratelimiter_allow (ratelimiter.c:84-156): the per-`(net, ip)` token
    bucket. The `(net, ip)` hsiphash is a cut and there is one netns per trace,
    so the mirror keys by source IP. On a bucket hit: refill
    `min(TOKEN_MAX, tokens + now - last)`, allow iff `>= PACKET_COST`, deduct. On
    a miss: insert (always allows the first packet). The 16384-entry table limit
    needs 16384 distinct source IPs — out of reach (the profound reason); the GC
    that frees stale entries arms a timer (D3), out of scope on this base. -/
def ratelimiterAllow (src : SkbSource) : M Bool := do
  -- the family switch (ratelimiter.c:95-109): IPv4 keys by the source address,
  -- IPv6 by the source /64 (`memcpy(&ip, &saddr, 8)`: the first eight bytes,
  -- the high 64 bits of the network-order address), each family in its own
  -- table (`table_v4`, `table_v6`; the bucket hash is a cut); another protocol
  -- returns false (:108-109), unreachable here: the skb came from one of the
  -- two UDP sockets
  let (v6, ip) ← do
    if ← branch .rlProtoIp (src.family == 4) then pure (false, src.saddr)
    else if ← branch .rlProtoIp6 (src.family == 6) then pure (true, src.saddr / 2 ^ 64)
    else invariant "a handshake skb that is neither IPv4 nor IPv6 at the ratelimiter"
  let table (k : WGWorld) : List (Nat × Int × Int) := if v6 then k.ratelimiter.table6 else k.ratelimiter.table
  let setTable (k : WGWorld) (t : List (Nat × Int × Int)) : WGWorld :=
    if v6 then { k with ratelimiter := { k.ratelimiter with table6 := t } }
    else { k with ratelimiter := { k.ratelimiter with table := t } }
  match (table (← get)).find? (·.1 == ip) with
  | some (_, tokens, lastTime) =>
    _ ← branch .rlEntryMatch true
    let now ← hiddenClock .ratelimiterNow
    let newTokens := min TOKEN_MAX (tokens + now - lastTime)
    let ret ← branchCmp .rlAllow (newTokens ≥ PACKET_COST) newTokens PACKET_COST
    let tokens' := if ret then newTokens - PACKET_COST else newTokens
    modify fun k => setTable k ((table k).map fun e => if e.1 == ip then (ip, tokens', now) else e)
    return ret
  | none =>
    -- `atomic_inc_return(&total_entries) > max_entries` (:135): one counter
    -- over both tables
    let k ← get
    let total := k.ratelimiter.table.length + k.ratelimiter.table6.length + 1
    if ← branchCmp .rlOverLimit (total > RL_MAX_ENTRIES) (Int.ofNat total) (Int.ofNat RL_MAX_ENTRIES) then
      unsupported "the ratelimiter table limit (16384 distinct source IPs — out of reach)"
    -- `kmem_cache_alloc(entry_cache, GFP_KERNEL)` (:138): an allocation
    -- outcome, kind 305, at this consumer frame (the hook is generic; the site
    -- is `AllocSite.kmemCacheAllocRlEntry`, armed by the ratelimiter traces'
    -- `draw` entries; B4, the receive audit's F13). On NULL, `err_oom`
    -- (:153-155): `atomic_dec(&total_entries)` (the mirror's count is the
    -- tables' size, so nothing to undo) and `return false`, which
    -- wg_cookie_validate_packet turns into VALID_MAC_WITH_COOKIE_BUT_RATELIMITED
    -- (cookie.c:146-148): the packet is dropped. The arm is reached only by
    -- steering, and the kworker class is not steerable (harness/steer.py
    -- ENABLED_CLASSES): declared, never taken on this host.
    if ← branch .rlAllocFail !(← hiddenAlloc .kmemCacheAllocRlEntry) then
      return false
    let now ← hiddenClock .ratelimiterInsertNow
    modify fun k => setTable k ((ip, TOKEN_MAX - PACKET_COST, now) :: table k)
    return true

/-- wg_cookie_validate_packet (cookie.c:119-154): the MAC1 check, and under
    load the MAC2 check (make_cookie, compute_mac2) and, on a valid MAC2, the
    ratelimiter (arm C). -/
def cookieValidatePacket (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) : M MacState := do
  let len := msg.length
  let computed := blake2s 16 (← getDev).mac1Key (msg.take (len - 32))
  let mac1 := (msg.drop (len - 32)).take 16
  if ← branch .macInvalid (computed != mac1) then return .invalid   -- crypto_memneq
  if ← branch .macNoCookieCheck (!checkCookie) then return .noCookie   -- !check_cookie → goto out
  -- under load: make_cookie, compute_mac2, crypto_memneq
  let cookie ← makeCookie src
  let computed2 := blake2s 16 cookie (msg.take (len - 16))
  let givenMac2 := (msg.drop (len - 16)).take 16
  if ← branch .macCookieInvalid (computed2 != givenMac2) then return .noCookie
  -- VALID_MAC_WITH_COOKIE_BUT_RATELIMITED unless wg_ratelimiter_allow permits
  -- `if (!wg_ratelimiter_allow(skb, net)) goto out` (cookie.c:147-148): the
  -- verdict is a declared decision (the receive audit's F2)
  if ← branch .macRatelimited !(← ratelimiterAllow src) then return .ratelimited
  return .withCookie

/-- wg_socket_send_buffer_as_reply_to_skb (socket.c:203-233): the reply goes to
    the initiating skb's endpoint (the flooding/injecting fixture sender). The
    GFP_ATOMIC `alloc_skb` (socket.c:217) is A's `replySkb` allocation site
    (docs/2026-10-05-a-alloc.md, 6.1); `send4`/`send6` are a cut, as in
    `sendBufferToPeer`. The function is not listed in the correspondence map, so
    only `wg_socket_endpoint_from_skb`'s decisions are checked for it. -/
def sendBufferAsReplyToSkb (src : SkbSource) (buffer : List UInt8) : M Unit := do
  -- `if (unlikely(!in_skb)) return -EINVAL` (socket.c:211-212): the receive
  -- path always hands an skb, so the false arm is the one taken
  if ← branch .replyInSkbNull false then invariant "a cookie reply without an skb"
  let endpoint ← endpointFromSkb src
  -- `if (unlikely(ret < 0)) return ret` (:214-215): endpoint_from_skb fails for
  -- neither family, unreachable from the two UDP sockets
  if ← branch .replyEndpointErr endpoint.isNone then
    invariant "a cookie reply to an skb that is neither IPv4 nor IPv6"
  let some e := endpoint | invariant "unreachable"
  -- `alloc_skb(len + SKB_HEADER_LEN, GFP_ATOMIC)` (:217-219): NULL returns
  -- -ENOMEM, which the caller ignores (receive.c), so no reply is sent. The
  -- record is A's `replySkb` site (exact 2) and the arm a declared decision;
  -- the function is listed since 2026-10-14 (the receive audit's F3).
  if ← branch .replyNoMem !(← hiddenAlloc .replySkb) then return
  -- the family switch (:224-227): send4/send6 (Socket.lean) with no cache on
  -- the endpoint built from the skb (W9); E's lax NET_RX cut is kept for this
  -- path (`exactRx := false`). The result is the caller's to ignore.
  if ← branch .replyInet (e.family == AF_INET) then _ ← send4 e none buffer 0 false
  else if ← branch .replyInet6 (e.family == AF_INET6) then _ ← send6 e none buffer 0 false

/-- wg_cookie_message_create (cookie.c:180-196): header 3 ‖ receiver index ‖
    nonce (`get_random_bytes_wait`, `.cookieNonce`) ‖ `xchacha20poly1305_encrypt`
    of make_cookie's cookie under the device's cookie-encryption key, AAD =
    the initiation's MAC1. -/
def cookieMessageCreate (index : Nat) (src : SkbSource) (mac1 : List UInt8) : M (List UInt8) := do
  let nonce ← hidden .cookieNonce
  let cookie ← makeCookie src
  let sealed := xchachaEncrypt (← getDev).cookieEncryptionKey nonce cookie mac1
  return le32 MESSAGE_HANDSHAKE_COOKIE ++ le32 index ++ nonce ++ sealed

/-- wg_packet_send_handshake_cookie (send.c:110-122): build the reply naming the
    initiation's `sender_index`, with AAD the initiation's MAC1, and send it. -/
def sendHandshakeCookie (msg : List UInt8) (src : SkbSource) : M Unit := do
  let index := u32le msg 4
  let mac1 := (msg.drop (msg.length - 32)).take 16
  sendBufferAsReplyToSkb src (← cookieMessageCreate index src mac1)

/-- wg_receive_handshake_packet (receive.c:92-204). -/
def receiveHandshakePacket (msg : List UInt8) (src : SkbSource) : M Unit := do
  if ← branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE) then
    cookieMessageConsume msg
    return
  -- `under_load = handshake_queue_len >= MAX_QUEUED_INCOMING_HANDSHAKES / 8`
  -- (receive.c:112): the counter, which a `wg_flood`'s batch has filled before
  -- the worker runs (E-B v2, the queue-depth design).
  let mut underLoad := false
  -- the compare's operands: the counter (an int) against the constant 512,
  -- compiled `> 511`, which the check's `ge` shift absorbs (declared 2026-10-14)
  let queueLen := (← getDev).handshakeQueueLen
  if ← branchCmp .hsUnderLoad (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
        (Int.ofNat queueLen) (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8)) then
    -- `last_under_load = ktime_get_coarse_boottime_ns()` (receive.c:115)
    let now ← hiddenClock64 .underLoadNow
    modify fun w => { w with lastUnderLoad := some now }
    underLoad := true
  -- `else if (last_under_load)`: the function-static (receive.c:100), nonzero
  -- after a flood this trace ran (every normal trace keeps it `none`, §4.2).
  else if ← branch .hsWasUnderLoad (← get).lastUnderLoad.isSome then
    let some last := (← get).lastUnderLoad | invariant "unreachable"
    -- `under_load = !wg_birthdate_has_expired(last_under_load, 1)` (receive.c:117),
    -- the recorded clock against the saved time; `if (!under_load)
    -- last_under_load = 0` (receive.c:118-119): the decay's reset
    let (expired, lhs, now) ← birthdateTest last 1
    underLoad := !expired
    -- the age test's operands are recorded at receive.c:117 (`Decision.comparison`'s site)
    if ← branchCmp .hsDecayExpired expired lhs now then
      modify fun w => { w with lastUnderLoad := none }
  let macState ← cookieValidatePacket msg src underLoad
  -- packet_needs_cookie (receive.c:123-132):
  -- `(under_load && mac == WITH_COOKIE) || (!under_load && mac == NO_COOKIE)`
  let proceed ← orM (andM (branch .hsLoadedOperand underLoad) (branch .hsLoadedCookieOk (macState == .withCookie)))
                    (andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (macState == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    -- `else if (under_load && mac == VALID_MAC_BUT_NO_COOKIE)`
    else if ← andM (branch .hsNeedsCookieLoaded underLoad) (branch .hsNeedsCookieMac (macState == .noCookie)) then
      pure true
    else return   -- invalid MAC: the packet is dropped
  let t := messageType msg
  let peer ← do
    if ← branch .hsSwitchInitiation (t == MESSAGE_HANDSHAKE_INITIATION) then
      if ← branch .hsInitNeedsCookie needsCookie then
        sendHandshakeCookie msg src
        return
      let peer ← consumeInitiation msg
      if ← branch .hsInitNoPeer peer.isNone then return
      let some pid := peer | invariant "unreachable"
      setPeerEndpointFromSkb pid src
      sendHandshakeResponse pid
      pure peer
    else if ← branch .hsSwitchResponse (t == MESSAGE_HANDSHAKE_RESPONSE) then
      if ← branch .hsRespNeedsCookie needsCookie then
        sendHandshakeCookie msg src
        return
      let peer ← consumeResponse msg
      if ← branch .hsRespNoPeer peer.isNone then return
      let some pid := peer | invariant "unreachable"
      setPeerEndpointFromSkb pid src
      if ← branch .hsRespSessionBegun (← beginSession pid) then
        timersSessionDerived pid
        timersHandshakeComplete pid
        -- either sends the staged packets or stages a keepalive and sends it
        sendKeepalive pid
      pure peer
    else pure none
  if ← branch .hsWrongPacket peer.isNone then invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  -- update_rx_stats: peer->rx_bytes (wg0's own rx counters,
  -- dev_sw_netstats_rx_add, are not tracked: nothing reads them on the
  -- modeled paths)
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + msg.length }
  -- update_rx_stats (receive.c:198): the device tstats too (W5, 2.6)
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  peerPut peer

/-- One iteration of wg_packet_handshake_receive_worker (receive.c:206-218):
    the ring poll (`false` when empty) and the handshake packet consumed.
    The environment runs the worker when the queued work runs. -/
def receiveStep : M Bool := do
  -- `ptr_ring_consume_bh` (ptr_ring.h:361-370): the peek, and on an item the
  -- discard that leaves its slot occupied until the batch rule clears it
  match (← getDev).handshakeQueue.consume with
  | (none, _) => do
    _ ← branch .workerConsumed false
    return false
  | (some (msg, src), ring) =>
    _ ← branch .workerConsumed true   -- ptr_ring_consume_bh: the ring slot is taken first
    modifyDev fun d => { d with handshakeQueue := ring }
    receiveHandshakePacket msg src
    -- dev_kfree_skb; atomic_dec(&handshake_queue_len) (receive.c:215)
    modifyDev fun d => { d with handshakeQueueLen := d.handshakeQueueLen - 1 }
    return true

/-- The whole loop: `receiveStep` per item, then `condResched`
    (receive.c:216: other kworkers may run here, the environment decides;
    W7 phase 2 interleaves the iterations, `workerIter`). The C's loop is
    unbounded and ends at the first NULL poll; the fuel is the ring's
    capacity plus that poll (a full ring takes 4097 iterations). -/
def handshakeReceiveWorker [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (condResched : m Unit) : m Unit :=
  workerLoop .receiveWorker none receiveStep condResched
    (MAX_QUEUED_INCOMING_HANDSHAKES + 1) "the handshake queue did not drain"

/-- wg_queue_enqueue_per_device_and_peer (queueing.h:157-178) for the
    decrypt queue and the peer's `rx_queue`: 0, `-ENOSPC` when the peer's
    `rx_queue` holds `MAX_QUEUED_PACKETS` (the 1025th item of one batch, the
    tier's `w7_ring_rx_1025`), or `-EPIPE` when the decrypt ring's slot is
    occupied (the 1024-item tier). -/
def enqueuePerDeviceAndPeerRx (id : SkbId) : M Int := do
  -- atomic_set_release(&PACKET_CB(skb)->state, PACKET_STATE_UNCRYPTED)
  setRxSkb id fun p => { p with state := .uncrypted }
  let pkt ← getRxSkb id
  let p ← getPeer pkt.peer
  -- `!wg_prev_queue_enqueue(peer_queue, skb)`: the queue's count is at MAX_QUEUED_PACKETS
  if ← branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) then return -ENOSPC
  setPeer pkt.peer { p with rxQueue := p.rxQueue.enqueue id }   -- W7: a multi-item queue
  let d ← getDev
  let cpu ← cpumaskNextOnlineFrom d.decryptLastCpu
  modifyDev fun d => { d with decryptLastCpu := cpu }
  -- `ptr_ring_produce_bh`: the producer's slot is occupied (`PtrRing.full`)
  if ← branch .enqueueRingFull d.decryptQueue.full then return -EPIPE
  -- queue_work_on(cpu, wq, &per_cpu_ptr(device_queue->worker, cpu)->work):
  -- queued iff not pending, with its record (dispatch order); the
  -- environment runs the decrypt worker while its ring holds packets
  queueDeviceWork .decryptWorker
  modifyDev fun d => { d with decryptQueue := d.decryptQueue.produce id }
  return 0

/-- wg_queue_enqueue_per_peer_rx (queueing.h:190-203): the packet's state is
    published on its peer's `rx_queue` and the peer's NAPI scheduled. `irqExit`
    is the environment's placement of an interrupt's exit at
    `__napi_schedule`'s `local_irq_restore` (D2, (c')). W7: the packet may be
    peeked (an UNCRYPTED head the poll stopped at) or queued; the oldest
    still-UNCRYPTED packet of its keypair is the one the worker holds, since
    both the ring and the queue are FIFO. -/
def enqueuePerPeerRx [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m] (irqExit : m Unit) (id : SkbId) (state : PacketState) : m Unit := do
  let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)   -- PACKET_PEER(skb)
  peerGet pid
  let p ← getPeer pid
  -- atomic_set_release(&PACKET_CB(skb)->state, state): the one skb the
  -- peer's rx_queue (queued or peeked, W7) and the worker name (review 4.2)
  if !(p.rxQueue.all.contains id) then
    invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb id fun q => { q with state }
  -- napi_schedule: NAPI_STATE_SCHED, and NET_RX raised (a cut point)
  setPeer pid { p with napiScheduled := true }
  irqExit
  peerPut (some pid)

/-- wg_packet_consume_data (receive.c:509-540). The keypair (with its peer
    referenced by the lookup) and a keypair reference go with the skb to the
    decrypt worker and the NAPI poll, which drop them. -/
def consumeData (msg : List UInt8) (src : SkbSource) (ds : Nat) : M Unit := do
  -- `data->key_idx`, of a keypair; the lookup takes a reference to the peer
  let entry ← indexLookup [.keypair] (u32le msg 4)
  -- `PACKET_CB(skb)->keypair = (struct noise_keypair *)entry` (the owner),
  -- `peer` the lookup's reference (peerlookup.c:220)
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (IndexOwner.keypair kp, pid) => pure (some kp, some pid)
    | some (IndexOwner.handshake _, _) => invariant "a handshake entry under the keypair mask"
  -- `unlikely(!wg_noise_keypair_get(PACKET_CB(skb)->keypair))`
  let kp ← match keypair with
    | none => do keypairGetNull; pure none   -- wg_noise_keypair_get(NULL)
    | some kp => keypairGet (some kp)
  if ← branch .dataNoKeypair kp.isNone then
    -- err_keypair: wg_peer_put(peer), then dev_kfree_skb
    peerPut peer
    return
  let some id := kp | invariant "unreachable"
  let some pid := peer | invariant "a keypair entry without a peer"
  if ← branch .dataPeerDead (← getPeer pid).isDead then
    -- err: the keypair's put, then err_keypair
    keypairPut (some id) false
    peerPut peer
    return
  -- PACKET_CB(skb)->keypair = keypair: the skb enters the store (review 4.2)
  let skb ← newRxSkb { peer := pid, keypair := id, bytes := msg, source := src, ds }
  let ret ← enqueuePerDeviceAndPeerRx skb
  -- `unlikely(ret == -EPIPE)`: wg_queue_enqueue_per_peer_rx(skb, PACKET_STATE_DEAD),
  -- whose napi_schedule in this softirq is polled by the same net_rx_action
  -- pass (W7, 5.2; the ring is full only on the 1024-item tier)
  if ← branch .dataEpipe (ret == -EPIPE) then enqueuePerPeerRx (pure ()) skb .dead
  -- `likely(!ret || ret == -EPIPE)`
  if ← orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
  -- err: (receive.c:534-539; `-ENOSPC`, the peer's rx_queue at
  -- MAX_QUEUED_PACKETS): the keypair's put, err_keypair's peer put, and
  -- dev_kfree_skb; a silent drop, no counter (the tx twin: `createData`).
  -- Found by the receive correspondence audit (F1): the arm was an
  -- `invariant` stop while the enqueue above returns `-ENOSPC`.
  keypairPut (some id) false
  peerPut peer
  freeRxSkb skb

/-- wg_cpumask_next_online (queueing.h:125-132) on this single-CPU kernel:
    `cpumask_next(n)` is `n + 1` and `nr_cpu_ids` is 1. -/
def cpumaskNextOnline : M Unit := do
  let next := (← getDev).handshakeLastCpu + 1
  let cpu ← do
    if ← branch .cpumaskWrap (next ≥ 1) then pure (0 : Int) else pure next
  modifyDev fun d => { d with handshakeLastCpu := cpu }

/-- The first two bytes of the outer IP header as far as its DS field goes
    (IPv4: version/IHL and TOS; IPv6: version, traffic class and the flow
    label's top bits as zero), for `ip_tunnel_get_dsfield`. -/
def outerDsBytes (src : SkbSource) : List UInt8 :=
  if src.family == 4 then [0x45, UInt8.ofNat src.tos]
  else [UInt8.ofNat (0x60 + src.tos / 16), UInt8.ofNat (src.tos % 16 * 16)]

/-- wg_packet_receive (receive.c:542-586). -/
def packetReceive (msg : List UInt8) (src : SkbSource) : M Unit := do
  if ← branch .rxPrepareFailed !(← prepareSkbHeader msg) then return   -- err: dev_kfree_skb
  let t := messageType msg
  if ← branch .rxHandshake (t == MESSAGE_HANDSHAKE_INITIATION || t == MESSAGE_HANDSHAKE_RESPONSE
                            || t == MESSAGE_HANDSHAKE_COOKIE) then
    if ← branch .rxRngNotReady false then unsupported "unreachable"   -- the guest waits for the RNG
    -- `handshake_queue_len > MAX_QUEUED_INCOMING_HANDSHAKES / 2` (the counter,
    -- against 2048): the trylock path (:555-558). `spin_trylock_bh` is on
    -- `producer_lock`, which only producers take, and on this configuration
    -- (no CONFIG_SMP, no CONFIG_DEBUG_SPINLOCK) `arch_spin_trylock` is
    -- `({ barrier(); (void)(lock); 1; })` (include/linux/spinlock_up.h:56):
    -- it always succeeds, and `__ptr_ring_produce` runs as the plain path's
    -- `ptr_ring_produce_bh` does (B4, section 2.5; reached from the 2,050th
    -- packet of a flood, which runs exactly since B4 part 2). An SMP oracle
    -- would need a record here.
    _ ← branch .rxQueueBusy ((← getDev).handshakeQueueLen > MAX_QUEUED_INCOMING_HANDSHAKES / 2)
    -- `__ptr_ring_produce` (ptr_ring.h:104-116) fails when the producer's
    -- slot is occupied (`PtrRing.full`): the packet is dropped (:561-565,
    -- dev_kfree_skb at :585) and the counter is not touched (B1)
    if ← branch .rxProduceFailed (← getDev).handshakeQueue.full then return   -- drop
    -- the produce, then atomic_inc(&wg->handshake_queue_len) (receive.c:567)
    modifyDev fun d => { d with handshakeQueue := d.handshakeQueue.produce (msg, src),
                                handshakeQueueLen := d.handshakeQueueLen + 1 }
    cpumaskNextOnline
    -- queue_work_on(cpu, handshake_receive_wq, ...): queued iff not pending,
    -- with its record (dispatch order); the environment runs the worker
    queueDeviceWork .receiveWorker
    return
  if ← branch .rxData (t == MESSAGE_DATA) then
    -- `PACKET_CB(skb)->ds = ip_tunnel_get_dsfield(ip_hdr(skb), skb)` (its
    -- inline decisions are stream A's, shared with send.c:378) of the outer
    -- header, whose DS field the environment gives in `src`
    let ds ← ipTunnelGetDsfield (if src.family == 4 then ETH_P_IP else ETH_P_IPV6) (outerDsBytes src)
    consumeData msg src ds
    return
  invariant "validate_header_len admitted an unknown type"

/-- wg_receive (socket.c:316-332), the UDP tunnel's `encap_rcv`. -/
def wgReceive (msg : List UInt8) (src : SkbSource) : M Unit := do
  if ← branch .rxNoSock false then unsupported "unreachable"
  if ← branch .rxNoWg false then unsupported "unreachable"
  packetReceive msg src

end Leanux.WG
