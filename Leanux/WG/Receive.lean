import Leanux.WG.Handshake

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
def MAX_QUEUED_INCOMING_HANDSHAKES : Nat := 4096

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
  let some e := entry | invariant "unreachable"
  let pid := e.peer
  let p ← getPeer pid
  if ← branch .cookieNoMac1Sent !p.haveSentMac1 then
    peerPut (some pid)   -- goto out
    return
  -- xchacha20poly1305_decrypt(cookie, encrypted_cookie, 32, last_mac1_sent,
  -- COOKIE_LEN, nonce, cookie_decryption_key)
  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent
  if ← branch .cookieDecryptOk cookie.isSome then
    let some c := cookie | invariant "unreachable"
    let birthdate ← hiddenClock .cookieBirthdate
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

/-- make_cookie (cookie.c:91-117): `blake2s_128(key = checker->secret,
    src_ip ‖ src_port)`. The secret-age read (`wg_birthdate_has_expired`,
    cookie.c:96 → timers.h:28) is a recorded `.birthdateExpired`; the 120 s
    rotation never fires in a 4 s trace. make_cookie is an out-of-line static
    the check does not list, so its protocol branch is not reported; its only
    checked effect is the cookie bytes (the reply's observable). -/
def makeCookie (src : SkbSource) : M (List UInt8) := do
  _ ← hiddenClock .birthdateExpired   -- wg_birthdate_has_expired(secret_birthdate, 120)
  let secret := (← getDev).cookieSecret
  let addr := if src.family == 4 then netBytes src.saddr 4 else netBytes src.saddr 16
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
  if ← branch .rlProtoIp (src.family == 4) then pure ()
  else unsupported "the ratelimiter on a non-IPv4 handshake (arm C is IPv4)"
  let ip := src.saddr
  match (← getK).ratelimiter.table.find? (·.1 == ip) with
  | some (_, tokens, lastTime) =>
    _ ← branch .rlEntryMatch true
    let now ← hiddenClock .ratelimiterNow
    let newTokens := min TOKEN_MAX (tokens + now - lastTime)
    let ret ← branchCmp .rlAllow (newTokens ≥ PACKET_COST) newTokens PACKET_COST
    let tokens' := if ret then newTokens - PACKET_COST else newTokens
    modifyK fun k => { k with ratelimiter := { k.ratelimiter with
      table := k.ratelimiter.table.map fun e => if e.1 == ip then (ip, tokens', now) else e } }
    return ret
  | none =>
    let total := (← getK).ratelimiter.table.length + 1
    if ← branchCmp .rlOverLimit (total > RL_MAX_ENTRIES) (Int.ofNat total) (Int.ofNat RL_MAX_ENTRIES) then
      unsupported "the ratelimiter table limit (16384 distinct source IPs — out of reach)"
    if ← branch .rlAllocFail !(← envOk .ratelimiterEntry) then
      unsupported "a ratelimiter entry allocation failure (-ENOMEM)"
    let now ← hiddenClock .ratelimiterInsertNow
    modifyK fun k => { k with ratelimiter := { k.ratelimiter with
      table := (ip, TOKEN_MAX - PACKET_COST, now) :: k.ratelimiter.table } }
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
  if ← ratelimiterAllow src then return .withCookie else return .ratelimited

/-- wg_socket_send_buffer_as_reply_to_skb (socket.c:203-233): the reply goes to
    the initiating skb's endpoint (the flooding/injecting fixture sender). The
    GFP_ATOMIC `alloc_skb` (socket.c:217) is A's `replySkb` allocation site
    (docs/2026-10-05-a-alloc.md, 6.1); `send4`/`send6` are a cut, as in
    `sendBufferToPeer`. The function is not listed in the correspondence map, so
    only `wg_socket_endpoint_from_skb`'s decisions are checked for it. -/
def sendBufferAsReplyToSkb (src : SkbSource) (buffer : List UInt8) : M Unit := do
  let endpoint ← endpointFromSkb src
  let some e := endpoint | invariant "a cookie reply to an skb that is neither IPv4 nor IPv6"
  -- `alloc_skb(len + SKB_HEADER_LEN, GFP_ATOMIC)` (socket.c:217): NULL returns
  -- -ENOMEM, which the caller ignores (receive.c), so no reply is sent. The
  -- record is consumed as A's table declares (`replySkb`, exact 2); the arm is
  -- not a declared decision because the function is unlisted (follow-up: list
  -- it and declare the arm, as `.sendBufNoMem` is for socket.c:192)
  -- [AGENT, int-e merge].
  if !(← hiddenAlloc .replySkb) then return
  skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]
  let sport ← socketPort e.family
  -- iptunnel_xmit_stats: the device tstats (W5, 2.6)
  modifyDev fun d => { d with txPackets := d.txPackets + 1, txBytes := d.txBytes + buffer.length }
  modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes := buffer, sport, src := e.src }] }

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
  -- `under_load = handshake_queue_len >= MAX_QUEUED_INCOMING_HANDSHAKES / 8`.
  -- A `wg_flood` adds `floodDepth` invalid packets ahead of the checked leading
  -- packet, so its queue is over the threshold (E-B §4.1, queue-depth design).
  let queueLen := (← getDev).handshakeQueue.length + (← get).floodDepth
  let mut underLoad := false
  if ← branch .hsUnderLoad (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8) then
    -- `last_under_load = ktime_get_coarse_boottime_ns()` (receive.c:115)
    let now ← hiddenClock .underLoadNow
    modify fun w => { w with lastUnderLoad := some now }
    underLoad := true
  -- `else if (last_under_load)`: a kernel-global, set by a flood this trace ran.
  -- Every normal trace keeps it `none` (the constant-false decay guard, §4.2).
  else if ← branch .hsWasUnderLoad (← get).lastUnderLoad.isSome then
    -- `under_load = !wg_birthdate_has_expired(last_under_load, 1)` (receive.c:117):
    -- the clock is read (`.birthdateExpired`); its comparison operand is a cut
    -- (the flood that set `last_under_load` is discarded), and the generator
    -- places the injection within the decay so `under_load` is true (§4.1).
    _ ← hiddenClock .birthdateExpired
    underLoad := true
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

/-- wg_packet_handshake_receive_worker (receive.c:206-218): drains the
    handshake queue. The environment runs it when the queued work runs. -/
def handshakeReceiveWorker (condResched : M Unit) : M Unit := do
  for _ in [0:MAX_QUEUED_INCOMING_HANDSHAKES] do
    match (← getDev).handshakeQueue with
    | [] => do
      _ ← branch .workerConsumed false
      return
    | (msg, src) :: _ =>
      _ ← branch .workerConsumed true   -- ptr_ring_consume_bh
      receiveHandshakePacket msg src
      -- dev_kfree_skb; atomic_dec(&handshake_queue_len)
      modifyDev fun d => { d with handshakeQueue := d.handshakeQueue.drop 1 }
      condResched   -- receive.c:216: other kworkers may run here (the environment decides)
  invariant "the handshake queue did not drain"

/-- wg_queue_enqueue_per_device_and_peer (queueing.h:157-178) for the
    decrypt queue and the peer's `rx_queue`: 0, or (outside the domain)
    `-ENOSPC` / `-EPIPE`. One item per queue is the domain (design section
    8): the decrypt worker of the previous injection has run. -/
def enqueuePerDeviceAndPeerRx (pkt : RxPacket) : M Int := do
  -- atomic_set_release(&PACKET_CB(skb)->state, PACKET_STATE_UNCRYPTED)
  let pkt := { pkt with state := .uncrypted }
  let p ← getPeer pkt.peer
  -- `!wg_prev_queue_enqueue(peer_queue, skb)`: the queue's count is at MAX_QUEUED_PACKETS
  if ← branch .enqueuePeerQueueFull (p.rxQueue.length ≥ MAX_QUEUED_PACKETS) then
    unsupported "a full rx_queue (-ENOSPC)"
  if !p.rxQueue.isEmpty then unsupported "more than one packet on a peer's rx_queue"
  setPeer pkt.peer { p with rxQueue := p.rxQueue ++ [pkt] }
  let d ← getDev
  let cpu ← cpumaskNextOnlineFrom d.decryptLastCpu
  modifyDev fun d => { d with decryptLastCpu := cpu }
  if ← branch .enqueueRingFull (d.decryptQueue.length ≥ MAX_QUEUED_PACKETS) then
    unsupported "a full decrypt ring (-EPIPE)"
  if !d.decryptQueue.isEmpty then unsupported "more than one item in the decrypt queue"
  -- queue_work_on(cpu, wq, &per_cpu_ptr(device_queue->worker, cpu)->work):
  -- the environment runs the decrypt worker while its ring holds packets
  modifyDev fun d => { d with decryptQueue := d.decryptQueue ++ [pkt] }
  return 0

/-- wg_packet_consume_data (receive.c:509-540). The keypair (with its peer
    referenced by the lookup) and a keypair reference go with the skb to the
    decrypt worker and the NAPI poll, which drop them. -/
def consumeData (msg : List UInt8) (src : SkbSource) (ds : Nat) : M Unit := do
  -- `data->key_idx`, of a keypair; the lookup takes a reference to the peer
  let entry ← indexLookup [.keypair] (u32le msg 4)
  let peer := entry.map (·.peer)
  -- `unlikely(!wg_noise_keypair_get(PACKET_CB(skb)->keypair))`
  let kp ← match entry with
    | none => do keypairGetCurrent; pure none   -- wg_noise_keypair_get(NULL)
    | some e => keypairGet e.keypair
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
  let ret ← enqueuePerDeviceAndPeerRx { peer := pid, keypair := id, bytes := msg, source := src, ds }
  -- `unlikely(ret == -EPIPE)`: wg_queue_enqueue_per_peer_rx(skb, PACKET_STATE_DEAD)
  if ← branch .dataEpipe (ret == -EPIPE) then invariant "unreachable"
  -- `likely(!ret || ret == -EPIPE)`
  if ← orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
  invariant "unreachable"

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
    let queueLen := (← getDev).handshakeQueue.length
    -- `handshake_queue_len > MAX_QUEUED_INCOMING_HANDSHAKES / 2`: the trylock path
    if ← branch .rxQueueBusy (queueLen > MAX_QUEUED_INCOMING_HANDSHAKES / 2) then
      unsupported "spin_trylock_bh on a busy handshake queue"
    -- ptr_ring_produce_bh fails when the ring (MAX_QUEUED_INCOMING_HANDSHAKES) is full
    if ← branch .rxProduceFailed (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES) then return   -- drop
    modifyDev fun d => { d with handshakeQueue := d.handshakeQueue ++ [(msg, src)] }
    cpumaskNextOnline
    -- queue_work_on(cpu, handshake_receive_wq, ...): the environment runs the worker
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
