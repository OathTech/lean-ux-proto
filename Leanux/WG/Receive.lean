import Leanux.WG.Send

/-!
# drivers/net/wireguard/receive.c — the receive path up to Noise

The fixture's sender delivers one UDP datagram to wg0's socket over loopback,
so the IP and UDP headers are well formed: `prepare_skb_header`'s header
checks hold, and only the WireGuard message itself varies. The handshake
worker's coverage reaches the trace through remote KCOV (the U2 kernel). Cut
points:
`ip_tunnel_parse_protocol`, `pskb_may_pull`/`pskb_trim` (the datagram is
linear and in bounds), the ptr ring, `queue_work_on`, `dev_kfree_skb`.

Queued handshake messages wait in the device's `handshakeQueue`; the
environment (`Leanux/Env.lean`) runs `handshakeReceiveWorker` when the queued
work runs, before the operation ends. A handshake message with a valid MAC1 enters Noise
(`wg_noise_handshake_consume_*`), stage C: `unsupported`. The index
hashtable's bucket walk is a cut point only while the table is empty; with an
entry (inserted under a random index by the handshake worker), the walk's path
is random and the lookup is `unsupported`.
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

/-- wg_index_hashtable_lookup (peerlookup.c:202-226) on the empty table. -/
def indexLookup : M (Option PeerId) := do
  for (_, p) in (← getDev).peers.toList do
    if p.indexed then unsupported "an index lookup with entries under random indices"
  -- the bucket is empty: `iter_entry->index == index` is never evaluated
  _ ← branch .idxFound false
  return none

/-- wg_cookie_message_consume (cookie.c:198-236). -/
def cookieMessageConsume : M Unit := do
  let peer ← indexLookup
  if ← branch .cookieLookupMiss peer.isNone then return
  unsupported "a cookie for a known index"

/-- wg_cookie_validate_packet (cookie.c:119-154) when not under load:
    whether MAC1 is valid. -/
def cookieValidatePacket (msg : List UInt8) : M Bool := do
  let len := msg.length
  let computed := blake2s 16 (← getDev).mac1Key (msg.take (len - 32))
  let mac1 := (msg.drop (len - 32)).take 16
  if ← branch .macInvalid (computed != mac1) then return false   -- crypto_memneq
  if ← branch .macNoCookieCheck true then return true            -- !check_cookie
  unsupported "unreachable"

/-- wg_receive_handshake_packet (receive.c:92-204). -/
def receiveHandshakePacket (msg : List UInt8) : M Unit := do
  if ← branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE) then
    cookieMessageConsume
    return
  -- `under_load = handshake_queue_len >= MAX_QUEUED_INCOMING_HANDSHAKES / 8`
  let queueLen := (← getDev).handshakeQueue.length
  if ← branch .hsUnderLoad (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8) then
    unsupported "a handshake queue under load"
  -- `else if (last_under_load)`: a kernel-global, zero while never under load
  _ ← branch .hsWasUnderLoad false
  let valid ← cookieValidatePacket msg
  -- `(under_load && mac_state == VALID_MAC_WITH_COOKIE) || (!under_load && mac_state == VALID_MAC_BUT_NO_COOKIE)`
  _ ← branch .hsLoadedOperand false
  if ← andM (branch .hsNotLoaded true) (branch .hsMacNoCookie valid) then
    unsupported "a handshake message with a valid MAC1 (Noise, stage C)"
  -- `else if (under_load && mac_state == VALID_MAC_BUT_NO_COOKIE)`
  _ ← branch .hsNeedsCookieLoaded false
  -- invalid MAC: the packet is dropped

/-- wg_packet_handshake_receive_worker (receive.c:206-218): drains the
    handshake queue. The environment runs it when the queued work runs. -/
def handshakeReceiveWorker : M Unit := do
  for _ in [0:MAX_QUEUED_INCOMING_HANDSHAKES] do
    match (← getDev).handshakeQueue with
    | [] => do
      _ ← branch .workerConsumed false
      return
    | msg :: _ =>
      _ ← branch .workerConsumed true   -- ptr_ring_consume_bh
      receiveHandshakePacket msg
      -- dev_kfree_skb; atomic_dec(&handshake_queue_len); cond_resched
      modifyDev fun d => { d with handshakeQueue := d.handshakeQueue.drop 1 }
  invariant "the handshake queue did not drain"

/-- wg_packet_consume_data (receive.c:509-540): no keypair has this index. -/
def consumeData : M Unit := do
  let _ ← indexLookup
  keypairGetCurrent   -- wg_noise_keypair_get(NULL)
  if !(← branch .dataNoKeypair true) then unsupported "a data keypair"
  -- err_keypair: wg_peer_put(NULL), then dev_kfree_skb
  peerPut none

/-- wg_cpumask_next_online (queueing.h:125-132) on this single-CPU kernel:
    `cpumask_next(n)` is `n + 1` and `nr_cpu_ids` is 1. -/
def cpumaskNextOnline : M Unit := do
  let next := (← getDev).handshakeLastCpu + 1
  let cpu ← do
    if ← branch .cpumaskWrap (next ≥ 1) then pure (0 : Int) else pure next
  modifyDev fun d => { d with handshakeLastCpu := cpu }

/-- wg_packet_receive (receive.c:542-586). -/
def packetReceive (msg : List UInt8) : M Unit := do
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
    modifyDev fun d => { d with handshakeQueue := d.handshakeQueue ++ [msg] }
    cpumaskNextOnline
    -- queue_work_on(cpu, handshake_receive_wq, ...): the environment runs the worker
    return
  if ← branch .rxData (t == MESSAGE_DATA) then
    -- ip_tunnel_get_dsfield (a cut point)
    consumeData
    return
  invariant "validate_header_len admitted an unknown type"

/-- wg_receive (socket.c:316-332), the UDP tunnel's `encap_rcv`. -/
def wgReceive (msg : List UInt8) : M Unit := do
  if ← branch .rxNoSock false then unsupported "unreachable"
  if ← branch .rxNoWg false then unsupported "unreachable"
  packetReceive msg

end Leanux.WG
