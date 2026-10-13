import Leanux.Proofs.WG.Lifetimes.CounterAccess
import Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Complete receive completion, including key rotation, staged sending,
maintenance and source routing. The returned bytes are a value; this module
does not claim delivery by the environment or order preservation. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

abbrev rxBranch (d : Decision) (b : Bool) : MixedM Bool := liftPrefix (branch d b)

def orPrefix (a b : MixedM Bool) : MixedM Bool := do if ← a then pure true else b

theorem orPrefix_erases (ha : ErasesPrefix a a') (hb : ErasesPrefix b b') :
    ErasesPrefix (orPrefix a b) (WG.orM a' b') := by
  apply erasesPrefix_bind ha
  intro first
  split
  · exact erasesPrefix_pure _
  · exact hb

theorem orPrefix_preserves (hs : ∀ h w, I h w → LifetimeEvent.Safe h)
    (ha : PrefixPreserves I LifetimeEvent.Safe a) (hb : PrefixPreserves I LifetimeEvent.Safe b) :
    PrefixPreserves I LifetimeEvent.Safe (orPrefix a b) := by
  apply PrefixPreserves.bind ha
  intro first
  split
  · exact PrefixPreserves.pure hs _
  · exact hb

def rxStatsUpdate (len : Nat) : Device → Device := fun d =>
  {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len}

structure RxContracts (I : List LifetimeEvent → World → Prop) : Prop where
  stats : ∀ len, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev (rxStatsUpdate len)))
  dishonest : ∀ why, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (WG.dishonest why))
  free : ∀ id, PrefixPreserves I LifetimeEvent.Safe (freeRxSkbPrefix id)

theorem allocationRx : RxContracts AllocationInv where
  stats := by
    intro len
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [rxStatsUpdate, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, rxStatsUpdate, Function.comp_def, Option.map_map] <;> rfl
  dishonest := by
    intro why
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    cases hr
    apply hi.congr
    · cases why <;> unfold identityView Peers.snapshot keypairResidents packetResidents <;>
        simp [Option.bind_map, Function.comp_def]
    · cases why <;> simp [allocationMetadata, deviceAllocationMetadata, Function.comp_def, Option.map_map] <;> rfl
  free := freeRxSkbPrefix_allocation

theorem inetEcnDecapsulate_sameKernel (protocol outer : Nat) (bytes : List UInt8) :
    SameKernel (inetEcnDecapsulate protocol outer bytes) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [inetEcnDecapsulate, inetEcnSet, ipEcnSetCe, ipEcnSetEct1,
    ip6EcnSetCe, ip6EcnSetEct1, branch]

def updateRxStatsPrefix (pid : PeerId) (len : Nat) : MixedM Unit := do
  liftPrefix (modifyDev (rxStatsUpdate len))
  modifyPeerKeysPrefix pid fun p => {p with rxBytes := p.rxBytes + len}

theorem updateRxStatsPrefix_erases (pid : PeerId) (len : Nat) :
    ErasesPrefix (updateRxStatsPrefix pid len) (updateRxStats pid len) :=
  erasesPrefix_bind (erasesPrefix_lift _) (fun _ => modifyPeerKeysPrefix_erases _ _)

theorem updateRxStatsPrefix_preserves (c : AmbientContracts I) (r : RxContracts I)
    (pid : PeerId) (len : Nat) : PrefixPreserves I LifetimeEvent.Safe (updateRxStatsPrefix pid len) :=
  PrefixPreserves.bind (r.stats len) (fun _ => AmbientContracts.drop
    (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid _ (fun _ => rfl)))

def consumeDataDonePrefix (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : MixedM (Option (List UInt8)) := do
  setPeerEndpointPrefix pid endpoint
  if ← rxBranch .doneReceivedNew (← receivedWithKeypairPrefix pid pkt.keypair) then
    timersHandshakeCompletePrefix pid .walltimeLastHandshakeData
    sendStagedPacketsPrefix pid
  keepKeyFreshRxPrefix pid
  timersAnyAuthenticatedPacketReceivedPrefix pid
  timersTraversalPrefix pid
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : MixedM (Option (List UInt8)) := do
    liftPrefix (dishonest why)   -- then packet_processed: dev_kfree_skb
    return none
  -- a packet with length 0 is a keepalive
  if ← rxBranch .doneRxKeepalive (len == 0) then
    updateRxStatsPrefix pid MESSAGE_DATA_LEN_0   -- message_data_len(0)
    return none
  timersDataReceivedPrefix pid
  -- `skb_network_header(skb) < skb->head`: the decrypted skb's network header is its data
  if ← rxBranch .doneNetworkBelowHead false then return ← reject .size
  -- `!(pskb_network_may_pull(skb, sizeof(struct iphdr)) && (version == 4 ||
  -- (version == 6 && pskb_network_may_pull(skb, sizeof(struct ipv6hdr)))))`
  let version := (bytes.headD 0).toNat / 16
  let honest ← andPrefix (rxBranch .doneMayPullV4 (len ≥ 20)) do
    orPrefix (rxBranch .doneVersion4 (version == 4)) do
      andPrefix (rxBranch .doneVersion6 (version == 6)) (rxBranch .doneMayPullV6 (len ≥ 40))
  if !honest then return ← reject .type
  -- skb->ip_summed = CHECKSUM_UNNECESSARY; csum_level = ~0
  let protocol := ipTunnelParseProtocol bytes
  let ds := pkt.ds   -- PACKET_CB(skb)->ds
  let mut ipLen := 0
  let mut bytes := bytes
  if ← rxBranch .doneProtoIp (protocol == 4) then
    ipLen := beAt bytes 2 2   -- ntohs(ip_hdr(skb)->tot_len)
    if ← rxBranch .doneV4TooShort (ipLen < 20) then return ← reject .size
    bytes ← liftPrefix (inetEcnDecapsulate 4 ds bytes)   -- INET_ECN_decapsulate(skb, ds, ip_hdr(skb)->tos)
  else if ← rxBranch .doneProtoIpv6 (protocol == 6) then
    ipLen := beAt bytes 4 2 + 40   -- ntohs(payload_len) + sizeof(struct ipv6hdr)
    bytes ← liftPrefix (inetEcnDecapsulate 6 ds bytes)   -- ..., ipv6_get_dsfield(ipv6_hdr(skb))
  else return ← reject .type
  if ← rxBranch .doneLenBeyond (ipLen > len) then return ← reject .size
  let lenBeforeTrim := len
  -- pskb_trim(skb, len) of a linear skb
  if ← rxBranch .doneTrimFailed false then return none
  let routed ← lookupSrcPrefix protocol bytes
  peerPutMixed routed   -- we don't need the extra reference
  if ← rxBranch .doneDishonestPeer (routed != some pid) then return ← reject .peer
  -- napi_gro_receive(&peer->napi, skb) (a cut point)
  updateRxStatsPrefix pid (lenBeforeTrim + MESSAGE_DATA_LEN_0)   -- message_data_len(len_before_trim)
  return some (bytes.take ipLen)

theorem consumeDataDonePrefix_erases (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    ErasesPrefix (consumeDataDonePrefix pid pkt e) (consumeDataDone pid pkt e) := by
  unfold consumeDataDonePrefix consumeDataDone
  repeat' first
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible exact setPeerEndpointPrefix_erases _ _
    | with_reducible exact receivedWithKeypairPrefix_erases _ _
    | with_reducible exact timersHandshakeCompletePrefix_erases _ _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact keepKeyFreshRxPrefix_erases _
    | with_reducible exact timersAnyAuthenticatedPacketReceivedPrefix_erases _
    | with_reducible exact timersTraversalPrefix_erases _
    | with_reducible exact updateRxStatsPrefix_erases _ _
    | with_reducible exact timersDataReceivedPrefix_erases _
    | with_reducible exact lookupSrcPrefix_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply orPrefix_erases
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (solve | simp_all)
    | (with_reducible intro x; try dsimp only)

theorem consumeDataDonePrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (r : RxContracts I) (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    PrefixPreserves I LifetimeEvent.Safe (consumeDataDonePrefix pid pkt e) := by
  have hq (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})) :=
    AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  unfold consumeDataDonePrefix
  repeat' first
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | with_reducible exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact receivedWithKeypairPrefix_preserves_ambient c t.put _ _
    | with_reducible exact AmbientContracts.drop (timersHandshakeCompletePrefix_spec c (fun _ => True) _ _)
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c t _
    | with_reducible exact keepKeyFreshRxPrefix_preserves_ambient c hq _
    | with_reducible exact AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _)
    | with_reducible exact updateRxStatsPrefix_preserves c r _ _
    | with_reducible exact AmbientContracts.drop (timersDataReceivedPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (lookupSrcPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact c.peerPut _
    | with_reducible exact r.dishonest _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (inetEcnDecapsulate_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
