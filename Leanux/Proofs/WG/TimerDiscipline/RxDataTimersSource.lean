import Leanux.Proofs.WG.TimerDiscipline.RxDataTimersModel
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

def rxDataTimersTail (pid : PeerId) (pkt : RxPacket) : WG.M (Option (List UInt8)) := do
  let bytes := pkt.bytes
  let len := bytes.length
  let reject (why : Dishonest) : WG.M (Option (List UInt8)) := do
    dishonest why
    return none
  -- `skb_network_header(skb) < skb->head`: the decrypted skb's network header is its data
  if ← branch .doneNetworkBelowHead false then return ← reject .size
  -- `!(pskb_network_may_pull(skb, sizeof(struct iphdr)) && (version == 4 ||
  -- (version == 6 && pskb_network_may_pull(skb, sizeof(struct ipv6hdr)))))`
  let version := (bytes.headD 0).toNat / 16
  let honest ← WG.andM (branch .doneMayPullV4 (len ≥ 20)) do
    WG.orM (branch .doneVersion4 (version == 4)) do
      WG.andM (branch .doneVersion6 (version == 6)) (branch .doneMayPullV6 (len ≥ 40))
  if !honest then return ← reject .type
  -- skb->ip_summed = CHECKSUM_UNNECESSARY; csum_level = ~0
  let protocol := ipTunnelParseProtocol bytes
  let ds := pkt.ds   -- PACKET_CB(skb)->ds
  let mut ipLen := 0
  let mut bytes := bytes
  if ← branch .doneProtoIp (protocol == 4) then
    ipLen := beAt bytes 2 2   -- ntohs(ip_hdr(skb)->tot_len)
    if ← branch .doneV4TooShort (ipLen < 20) then return ← reject .size
    bytes ← inetEcnDecapsulate 4 ds bytes   -- INET_ECN_decapsulate(skb, ds, ip_hdr(skb)->tos)
  else if ← branch .doneProtoIpv6 (protocol == 6) then
    ipLen := beAt bytes 4 2 + 40   -- ntohs(payload_len) + sizeof(struct ipv6hdr)
    bytes ← inetEcnDecapsulate 6 ds bytes   -- ..., ipv6_get_dsfield(ipv6_hdr(skb))
  else return ← reject .type
  if ← branch .doneLenBeyond (ipLen > len) then return ← reject .size
  let lenBeforeTrim := len
  -- pskb_trim(skb, len) of a linear skb
  if ← branch .doneTrimFailed false then return none
  let routed ← lookupSrc protocol bytes
  peerPut routed   -- we don't need the extra reference
  if ← branch .doneDishonestPeer (routed != some pid) then return ← reject .peer
  -- napi_gro_receive(&peer->napi, skb) (a cut point)
  updateRxStats pid (lenBeforeTrim + MESSAGE_DATA_LEN_0)   -- message_data_len(len_before_trim)
  return some (bytes.take ipLen)

def rxDataTimersPrelude (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : WG.M Unit := do
  setPeerEndpoint pid endpoint
  if ← branch .doneReceivedNew (← receivedWithKeypair pid pkt.keypair) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid

def rxDataTimersPrefix (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : WG.M Bool := do
  rxDataTimersPrelude pid pkt endpoint
  timersTraversal pid
  let keepalive ← branch .doneRxKeepalive (pkt.bytes.length == 0)
  if keepalive then
    updateRxStats pid MESSAGE_DATA_LEN_0
    return true
  timersDataReceived pid
  return false

def rxDataTimersSuffix (pid : PeerId) (pkt : RxPacket) (keepalive : Bool) : WG.M (Option (List UInt8)) :=
  if keepalive then pure none else rxDataTimersTail pid pkt

theorem rxDataTimers_source (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    (rxDataTimersPrefix pid pkt e >>= rxDataTimersSuffix pid pkt) = consumeDataDone pid pkt e := by
  have bindIf {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : WG.M α) (next : α → WG.M β) :
      ((if condition then yes else no) >>= next) =
        (if condition then yes >>= next else no >>= next) := by
    split <;> rfl
  simp only [rxDataTimersPrefix, rxDataTimersPrelude, rxDataTimersSuffix, rxDataTimersTail,
    consumeDataDone, bind_assoc, bindIf, pure_bind, Bool.false_eq_true, ite_false, ite_true]

def rxDataTimersObservedPrefix (pid : PeerId) (pkt : RxPacket) (e : Endpoint) : Leanux.M RxDataTimersCut := do
  liftWG (rxDataTimersPrelude pid pkt e)
  let traversal ← dataDoneCapture (liftWG (timersTraversal pid))
    (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)
  let keepalive ← (branch .doneRxKeepalive (pkt.bytes.length == 0) : Leanux.M Bool)
  if keepalive then
    liftWG (updateRxStats pid MESSAGE_DATA_LEN_0)
    return ⟨traversal, none, true⟩
  let receipt ← dataDoneCapture (liftWG (timersDataReceived pid))
    (prefixClockPath (liftWG (dataReceivedPrefix pid)) .timerJiffiesDataReceived)
  return ⟨traversal, some receipt, false⟩

theorem rxDataTimersObservedPrefix_erase (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    (do let cut ← rxDataTimersObservedPrefix pid pkt e; pure cut.keepalive) = liftWG (rxDataTimersPrefix pid pkt e) := by
  have lift_pure {α : Type} (value : α) : liftWG (pure value) = (pure value : Leanux.M α) := rfl
  have lift_branch (decision : Decision) (value : Bool) :
      liftWG (branch decision value : WG.M Bool) = (branch decision value : Leanux.M Bool) := rfl
  simp only [rxDataTimersObservedPrefix, rxDataTimersPrefix, liftWG_bind_variant,
    lift_branch, bind_assoc, Roaming.bind_if, pure_bind]
  congr 1
  funext u
  rw [dataDoneCapture_bind]
  congr 1
  funext u
  congr 1
  funext keepalive
  cases keepalive
  · simp only [Bool.false_eq_true, ite_false, liftWG_bind_variant, lift_pure]
    exact dataDoneCapture_bind _ _ (pure false)
  · simp only [ite_true, liftWG_bind_variant, lift_pure]

/-- The decorated prefix feeds the unchanged native suffix at its actual state. -/
def observedRxDataTimers (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Leanux.M (RxDataTimersCut × Option (List UInt8)) := do
  let cut ← rxDataTimersObservedPrefix pid pkt e
  let result ← liftWG (rxDataTimersSuffix pid pkt cut.keepalive)
  return (cut, result)

/-- Erasure preserves the complete original return value and every error. -/
theorem observedRxDataTimers_erase (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    (do let observed ← observedRxDataTimers pid pkt e; pure observed.2) =
      liftWG (consumeDataDone pid pkt e) := by
  rw [← rxDataTimers_source pid pkt e, liftWG_bind_variant, ← rxDataTimersObservedPrefix_erase pid pkt e]
  simp only [observedRxDataTimers, bind_assoc, pure_bind, bind_pure]


end Leanux.Proofs.WG.TimerDiscipline
