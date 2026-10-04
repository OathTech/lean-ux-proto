import Leanux.WG.Handshake

/-!
# drivers/net/wireguard/send.c — the encrypt and tx workers

`wg_packet_create_data` (Send.lean) puts a packet on the device's encrypt
queue and on its peer's `tx_queue`. The environment (`Leanux/Env.lean`) runs
the encrypt worker, then the tx worker, as the kernel runs them on its one
CPU after the work that queued them.

`encrypt_packet` is mirrored with every value: the padding, the
`message_data` header and ChaCha20-Poly1305 of the padded plaintext under the
keypair's sending key (the NoiseCrypto reference). Cut points:
- `skb_get_hash` (flow dissection; it may draw the flow-hash secret once);
- the skb surgery `skb_cow_head`, `skb_cow_data` and `skb_to_sgvec`, whose
  failures are environment outcomes (`envOk`);
- `wg_reset_packet` (header resets; its `encapsulating` is the constant true);
- routing and the UDP tunnel transmit below `wg_socket_send_skb_to_peer`, as
  in `sendBufferToPeer` (Handshake.lean);
- `need_resched()`, a scheduler flag, reported false: a reschedule here would
  cover `cond_resched`'s line, which the check reports.

Only keepalives reach encryption in the domain (Send.lean), so a packet's
`PACKET_CB(skb)->mtu` is the device's (`DEVICE_MTU`).
-/

namespace Leanux.WG
open Leanux

def MESSAGE_DATA_TYPE : Nat := 4
def MESSAGE_PADDING_MULTIPLE : Nat := 16
/-- `message_data_len(0)`: the header and the authentication tag. -/
def MESSAGE_DATA_LEN_0 : Nat := 16 + 16

/-- `cpu_to_le64`. -/
def le64 (n : Nat) : List UInt8 := (List.range 8).map fun k => UInt8.ofNat (n / 256 ^ k % 256)

/-- The ChaCha20-Poly1305 nonce `chacha20poly1305_encrypt_sg_inplace` builds
    from a 64-bit counter: 4 zero bytes, then the counter little-endian. -/
def counterNonce (counter : Nat) : List UInt8 := List.replicate 4 0 ++ le64 counter

/-- `ALIGN(n, MESSAGE_PADDING_MULTIPLE)`. -/
def alignPadding (n : Nat) : Nat :=
  (n + MESSAGE_PADDING_MULTIPLE - 1) / MESSAGE_PADDING_MULTIPLE * MESSAGE_PADDING_MULTIPLE

/-- calculate_skb_padding (send.c:141-160). -/
def calculateSkbPadding (len mtu : Nat) : M Nat := do
  if ← branch .padNoMtu (mtu == 0) then return alignPadding len - len
  let lastUnit ← do
    if ← branch .padOverMtu (len > mtu) then pure (len % mtu) else pure len
  let paddedSize := min mtu (alignPadding lastUnit)
  return paddedSize - lastUnit

/-- The pure part of `encrypt_packet`: the `message_data` message for a
    packet's plaintext (already padded) under a keypair's remote index and
    sending key. -/
def dataMessage (remoteIndex nonce : Nat) (key plaintext : List UInt8) : List UInt8 :=
  le32 MESSAGE_DATA_TYPE ++ le32 remoteIndex ++ le64 nonce ++ aeadEncrypt key (counterNonce nonce) plaintext []

/-- encrypt_packet (send.c:162-219): the message bytes, or `none` when it
    fails. -/
def encryptPacket (pkt : DataPacket) : M (Option (List UInt8)) := do
  -- skb_get_hash (a cut point)
  skipCut [.flowHashSecret]
  if pkt.plaintextLen != 0 then invariant "a payload packet reached encryption"
  let paddingLen ← calculateSkbPadding pkt.plaintextLen DEVICE_MTU
  let plaintextLen := pkt.plaintextLen + paddingLen
  -- `skb_cow_head(skb, DATA_PACKET_HEAD_ROOM) < 0`
  if ← branch .encCowHeadFailed !(← envOk .skbCowHead) then return none
  -- `skb->ip_summed == CHECKSUM_PARTIAL && skb_checksum_help(skb)`: a
  -- keepalive's `ip_summed` is CHECKSUM_NONE
  if ← branch .encChecksumPartial false then
    if ← branch .encChecksumHelpFailed false then return none
  -- `num_frags = skb_cow_data(...)`: 1 (the keepalive is linear), or negative
  let cowOk ← envOk .skbCowData
  if ← branch .encCowDataFailed !cowOk then return none
  if ← branch .encTooManyFrags false then return none   -- num_frags > ARRAY_SIZE(sg)
  -- the zero padding, the header (`key_idx = keypair->remote_index`,
  -- `counter = cpu_to_le64(nonce)`) and room for the tag
  let k ← getKeypair pkt.keypair
  if ← branch .encSgvecFailed !(← envOk .skbToSgvec) then return none
  -- chacha20poly1305_encrypt_sg_inplace: the payload (empty) and its padding
  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key (List.replicate plaintextLen 0))

/-- wg_packet_encrypt_worker (send.c:287-309): drains the encrypt queue.
    Each ring item is one packet (Send.lean admits no more). -/
def encryptWorker : M Unit := do
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    match (← getDev).encryptQueue with
    | [] =>
      _ ← branch .encWorkerConsumed false   -- ptr_ring_consume_bh
      return
    | first :: rest =>
      _ ← branch .encWorkerConsumed true
      modifyDev fun d => { d with encryptQueue := rest }
      -- skb_list_walk_safe(first, skb, next)
      _ ← branch .encWorkerSkbIterate true
      let encrypted ← encryptPacket first
      let (pkt, state) ← do
        if ← branch .encWorkerEncrypted encrypted.isSome then
          -- wg_reset_packet(skb, true) (a cut point)
          _ ← branch .encWorkerSkbIterate false
          pure ({ first with bytes := encrypted.getD [] }, PacketState.crypted)
        else pure (first, PacketState.dead)   -- break
      enqueuePerPeerTx pkt state
      _ ← branch .encWorkerNeedResched false
  invariant "the encrypt queue did not drain"

/-- wg_socket_send_skb_to_peer (socket.c:168-187) of an encrypted packet:
    whether it returned 0. `send4`/`send6` are a cut point, as in
    `sendBufferToPeer`: the datagram is recorded in `World.sent`. Delivery
    over loopback runs the NET_RX softirq inside this worker's section. -/
def sendSkbToPeer (pid : PeerId) (bytes : List UInt8) : M Bool := do
  let p ← getPeer pid
  let family := (p.endpoint.map (·.family)).getD 0
  let sent ← do
    if ← branch .sendSkbInet (family == AF_INET) then pure true
    else if ← branch .sendSkbInet6 (family == AF_INET6) then pure true
    else pure false   -- dev_kfree_skb; -EAFNOSUPPORT
  -- send4/send6 choose the IP ident; the loopback delivery is a nested
  -- NET_RX section
  if sent then skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret, .sectionStart .netRx, .sectionStop .netRx]
  if ← branch .sendSkbOk sent then
    let some e := p.endpoint | invariant "unreachable"
    setPeer pid { p with txBytes := p.txBytes + bytes.length }
    modify fun w => { w with sent := w.sent ++ [{ family := e.family, addr := e.addr, port := e.port, bytes }] }
  return sent

/-- keep_key_fresh (send.c:124-139). -/
def keepKeyFresh (pid : PeerId) : M Unit := do
  let current := (← getPeer pid).keypairCurrent
  -- `keypair && is_valid && (sending_counter > REKEY_AFTER_MESSAGES ||
  -- (i_am_the_initiator && wg_birthdate_has_expired(birthdate, REKEY_AFTER_TIME)))`
  let send ← andM (branch .freshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    andM (branch .freshValid k.sending.isValid) do
      orM (branch .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES)) do
        andM (branch .freshInitiator k.iAmTheInitiator) do
          branch .freshExpired (← birthdateHasExpired k.sending.birthdate REKEY_AFTER_TIME)
  if ← branch .freshSend send then sendQueuedHandshakeInitiation pid false

/-- wg_packet_create_data_done (send.c:242-260) for a one-packet list. -/
def createDataDone (pid : PeerId) (pkt : DataPacket) : M Unit := do
  timersTraversal pid
  -- wg_timers_any_authenticated_packet_sent: del_timer
  _ ← branch .doneSkbIterate true
  let isKeepalive := pkt.bytes.length == MESSAGE_DATA_LEN_0
  let sent ← sendSkbToPeer pid pkt.bytes
  -- `likely(!wg_socket_send_skb_to_peer(...) && !is_keepalive)`
  let dataSent ← andM (branch .doneSendOk sent) (branch .doneNotKeepalive !isKeepalive)
  _ ← branch .doneSkbIterate false
  if ← branch .doneDataSent dataSent then unsupported "wg_timers_data_sent (a data packet's handshake timer)"
  keepKeyFresh pid

/-- wg_packet_tx_worker (send.c:262-285) for a peer: sends its encrypted
    packets in order, dropping the references `wg_packet_send_staged_packets`
    took. -/
def txWorker (pid : PeerId) : M Unit := do
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    -- wg_prev_queue_peek: `queue->peeked` is NULL (dropped after every
    -- packet, and never left set: see below)
    _ ← branch .prevQueuePeeked false
    let first := (← getPeer pid).txQueue.head?
    -- `(first = peek) != NULL && (state = ...) != PACKET_STATE_UNCRYPTED`
    let go ← andM (branch .txPacket first.isSome) do
      let some f := first | invariant "unreachable"
      if f.state == .uncrypted then unsupported "the tx worker meets an uncrypted packet (it stays peeked)"
      branch .txNotUncrypted true
    if !go then return
    let some pkt := first | invariant "unreachable"
    -- wg_prev_queue_drop_peeked
    setPeer pid { (← getPeer pid) with txQueue := (← getPeer pid).txQueue.drop 1 }
    if ← branch .txCrypted (pkt.state == .crypted) then createDataDone pid pkt
    -- else kfree_skb_list(first)
    keypairPut (some pkt.keypair) false
    peerPut (some pid)
    _ ← branch .txNeedResched false
  invariant "the tx queue did not drain"

-- The keepalive's message for a known key (cross-checked against
-- harness/noise.py's aead_encrypt in harness/test_d1_keepalive.py): key
-- bytes 0..31, remote index 0x04030201, nonce 0.
#guard (dataMessage 0x04030201 0 (List.range 32 |>.map UInt8.ofNat) []).length == MESSAGE_DATA_LEN_0
#guard (dataMessage 0x04030201 0 (List.range 32 |>.map UInt8.ofNat) []).take 16 ==
  [4, 0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0]

end Leanux.WG
