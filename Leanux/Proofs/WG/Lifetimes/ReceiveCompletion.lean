import Leanux.Proofs.WG.Lifetimes.CounterAccess
import Leanux.Proofs.WG.Lifetimes.AllowedLookupAccess
import Leanux.Proofs.WG.Lifetimes.TxStaging

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Complete receive completion, including key rotation, staged sending,
maintenance and source routing. The returned bytes are a value; this module
does not claim delivery by the environment or order preservation. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

abbrev rxBranch (d : Decision) (b : Bool) : MixedM Bool := liftWGPrefix (branch d b)

def orPrefix {m : Type → Type} [Monad m] (a b : m Bool) : m Bool := do
  if ← a then pure true else b

theorem orPrefix_erases {E S : Type} {a b : PrefixT E S Bool}
    {a' b' : StateT S (Except Stop) Bool}
    (ha : ErasesPrefix a a') (hb : ErasesPrefix b b') :
    ErasesPrefix (orPrefix a b) (orPrefix a' b') := by
  apply erasesPrefix_bind ha
  intro first
  split
  · exact erasesPrefix_pure _
  · exact hb

theorem orPrefix_preserves {S : Type} {I : List LifetimeEvent → S → Prop}
    {a b : PrefixT LifetimeEvent S Bool} (hs : ∀ h w, I h w → LifetimeEvent.Safe h)
    (ha : PrefixPreserves I LifetimeEvent.Safe a) (hb : PrefixPreserves I LifetimeEvent.Safe b) :
    PrefixPreserves I LifetimeEvent.Safe (orPrefix a b) := by
  apply PrefixPreserves.bind ha
  intro first
  split
  · exact PrefixPreserves.pure hs _
  · exact hb

theorem orPrefix_erases_state {E Outer Inner : Type}
    {a b : StatePrefixT E Outer Inner Bool}
    {a' b' : StateT Outer (StateT Inner (Except Stop)) Bool}
    (ha : ErasesStatePrefix a a') (hb : ErasesStatePrefix b b') :
    ErasesStatePrefix (orPrefix a b) (orPrefix a' b') := by
  apply erasesStatePrefix_bind ha
  intro first
  split
  · exact erasesStatePrefix_pure _
  · exact hb

theorem orPrefix_preserves_state {Outer Inner : Type}
    {I : List LifetimeEvent → Outer → Inner → Prop}
    {a b : StatePrefixT LifetimeEvent Outer Inner Bool}
    (hs : ∀ h w ambient, I h w ambient → LifetimeEvent.Safe h)
    (ha : StatePrefixPreserves I LifetimeEvent.Safe a) (hb : StatePrefixPreserves I LifetimeEvent.Safe b) :
    StatePrefixPreserves I LifetimeEvent.Safe (orPrefix a b) := by
  apply StatePrefixEnsures.bind ha
  intro first
  split
  · exact StatePrefixEnsures.pure _ hs (fun _ _ _ hi => hi)
  · exact hb

def rxStatsUpdate (len : Nat) : Device → Device := fun d =>
  {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len}

structure RxContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  stats : ∀ len, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (modifyDev (rxStatsUpdate len)))
  dishonest : ∀ why, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (WG.dishonest why))
  free : ∀ id, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (freeRxSkbPrefix id)

structure ProductRxContracts (I : List LifetimeEvent → World → Prop) : Prop where
  stats : ∀ len, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev (rxStatsUpdate len))))
  dishonest : ∀ why, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (WG.dishonest why)))
  free : ∀ id, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (freeRxSkbPrefix id))

theorem allocationRx : RxContracts AllocationInv where
  stats := by
    intro len
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [rxStatsUpdate, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, rxStatsUpdate, Function.comp_def, Option.map_map] <;> rfl
  dishonest := by
    intro why
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · cases why <;> unfold identityView Peers.snapshot keypairResidents packetResidents <;>
        simp [Option.bind_map, Function.comp_def]
    · cases why <;> simp [allocationMetadata, deviceAllocationMetadata, Function.comp_def, Option.map_map] <;> rfl
  free := freeRxSkbPrefix_allocation

theorem inetEcnDecapsulate_sameWGStore (protocol outer : Nat) (bytes : List UInt8) :
    SameWGStore (inetEcnDecapsulate protocol outer bytes) := by
  apply SameView.of_wp
  intro k
  mvcgen [inetEcnDecapsulate, inetEcnSet, ipEcnSetCe, ipEcnSetEct1,
    ip6EcnSetCe, ip6EcnSetEct1, branch, AmbientM.branch]

def updateRxStatsPrefix (pid : PeerId) (len : Nat) : MixedM Unit := do
  liftWGPrefix (modifyDev (rxStatsUpdate len))
  modifyPeerKeysPrefix pid fun p => {p with rxBytes := p.rxBytes + len}

theorem updateRxStatsPrefix_erases (pid : PeerId) (len : Nat) :
    ErasesStatePrefix (updateRxStatsPrefix pid len) (updateRxStats pid len) :=
  erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => modifyPeerKeysPrefix_erases _ _)

theorem updateRxStatsPrefix_preserves (c : AmbientContracts I) (r : RxContracts I)
    (pid : PeerId) (len : Nat) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (updateRxStatsPrefix pid len) :=
  StatePrefixEnsures.bind (r.stats len) (fun _ => AmbientContracts.drop
    (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid _ (fun _ => rfl)))

theorem updateRxStatsPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductRxContracts I)
    (pid : PeerId) (len : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (updateRxStatsPrefix pid len)) := by
  simp only [updateRxStatsPrefix, liftWGObserver_bind]
  exact PrefixPreserves.bind (r.stats len) (fun _ => ProductAmbientContracts.drop
    (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid _ (fun _ => rfl)))

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
    liftWGPrefix (dishonest why)   -- then packet_processed: dev_kfree_skb
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
    bytes ← liftWGPrefix (inetEcnDecapsulate 4 ds bytes)   -- INET_ECN_decapsulate(skb, ds, ip_hdr(skb)->tos)
  else if ← rxBranch .doneProtoIpv6 (protocol == 6) then
    ipLen := beAt bytes 4 2 + 40   -- ntohs(payload_len) + sizeof(struct ipv6hdr)
    bytes ← liftWGPrefix (inetEcnDecapsulate 6 ds bytes)   -- ..., ipv6_get_dsfield(ipv6_hdr(skb))
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
    ErasesStatePrefix (consumeDataDonePrefix pid pkt e) (consumeDataDone pid pkt e) := by
  have conditional {α : Type} (p : Prop) [Decidable p]
      {g h : MixedM α} {a b : WG.M α}
      (hg : p → ErasesStatePrefix g a) (hh : ¬p → ErasesStatePrefix h b) :
      ErasesStatePrefix (if p then g else h) (if p then a else b) := by
    split <;> simp_all
  unfold consumeDataDonePrefix consumeDataDone rxBranch
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head setPeerEndpointPrefix; exact setPeerEndpointPrefix_erases _ _)
    | (maintenance_head receivedWithKeypairPrefix; exact receivedWithKeypairPrefix_erases _ _)
    | (maintenance_head timersHandshakeCompletePrefix; exact timersHandshakeCompletePrefix_erases _ _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_erases _)
    | (maintenance_head keepKeyFreshRxPrefix; exact keepKeyFreshRxPrefix_erases _)
    | (maintenance_head timersAnyAuthenticatedPacketReceivedPrefix; exact timersAnyAuthenticatedPacketReceivedPrefix_erases _)
    | (maintenance_head timersTraversalPrefix; exact timersTraversalPrefix_erases _)
    | (maintenance_head updateRxStatsPrefix; exact updateRxStatsPrefix_erases _ _)
    | (maintenance_head timersDataReceivedPrefix; exact timersDataReceivedPrefix_erases _)
    | (maintenance_head lookupSrcPrefix; exact lookupSrcPrefix_erases _ _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head andPrefix; apply andPrefix_erases_state)
    | (maintenance_head orPrefix; apply orPrefix_erases_state)
    | (maintenance_head ite; apply conditional)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem consumeDataDonePrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (r : RxContracts I) (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (consumeDataDonePrefix pid pkt e) := by
  have hq (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})) :=
    AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  have conditional {α : Type} (p : Prop) [Decidable p] {a b : MixedM α}
      (ha : p → StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe a)
      (hb : ¬p → StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe b) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (if p then a else b) := by
    split <;> simp_all
  unfold consumeDataDonePrefix rxBranch
  repeat' first
    | unfold StatePrefixPreserves
    | (maintenance_head setPeerEndpointPrefix; exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head receivedWithKeypairPrefix; exact receivedWithKeypairPrefix_preserves_ambient c t.put _ _)
    | (maintenance_head timersHandshakeCompletePrefix; exact AmbientContracts.drop (timersHandshakeCompletePrefix_spec c (fun _ => True) _ _))
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c t _)
    | (maintenance_head keepKeyFreshRxPrefix; exact keepKeyFreshRxPrefix_preserves_ambient c hq _)
    | (maintenance_head timersAnyAuthenticatedPacketReceivedPrefix; exact AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec c (fun _ => True) _))
    | (maintenance_head timersTraversalPrefix; exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _))
    | (maintenance_head updateRxStatsPrefix; exact updateRxStatsPrefix_preserves c r _ _)
    | (maintenance_head timersDataReceivedPrefix; exact AmbientContracts.drop (timersDataReceivedPrefix_spec c (fun _ => True) _))
    | (maintenance_head lookupSrcPrefix; exact AmbientContracts.drop (lookupSrcPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_lift_action_head dishonest; exact r.dishonest _)
    | (maintenance_lift_action_head inetEcnDecapsulate; exact AmbientContracts.drop (c.store (fun _ => True) _ (inetEcnDecapsulate_sameWGStore _ _ _)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.branch (fun _ => True) _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w (_ : Ambient) hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head andPrefix; apply andPrefix_preserves_state (fun h w (_ : Ambient) hi => c.safe h w hi))
    | (maintenance_head orPrefix; apply orPrefix_preserves_state (fun h w (_ : Ambient) hi => c.safe h w hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => I h w))
    | (maintenance_head ite; apply conditional)
    | (maintenance_intro; try dsimp only)
    | split

theorem consumeDataDonePrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (r : ProductRxContracts I) (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (consumeDataDonePrefix pid pkt e)) := by
  have hq (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))) :=
    ProductAmbientContracts.drop (t.device (fun _ => True) (.handshake pid))
  have conditional {α : Type} (p : Prop) [Decidable p] {a b : PrefixM LifetimeEvent α}
      (ha : p → PrefixEnsures I LifetimeEvent.Safe a (fun _ => I))
      (hb : ¬p → PrefixEnsures I LifetimeEvent.Safe b (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (if p then a else b) (fun _ => I) := by
    split <;> simp_all
  have lifted_conditional {α : Type} (p : Prop) [Decidable p] {a b : MixedM α}
      (ha : p → PrefixEnsures I LifetimeEvent.Safe (liftWGObserver a) (fun _ => I))
      (hb : ¬p → PrefixEnsures I LifetimeEvent.Safe (liftWGObserver b) (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (if p then a else b)) (fun _ => I) := by
    split <;> simp_all
  have and_ok {a b : MixedM Bool}
      (ha : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver a) (fun _ => I))
      (hb : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver b) (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (andPrefix a b)) (fun _ => I) := by
    rw [liftWGObserver_andPrefix]
    exact andPrefix_preserves c.safe ha hb
  have or_ok {a b : MixedM Bool}
      (ha : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver a) (fun _ => I))
      (hb : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver b) (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (orPrefix a b)) (fun _ => I) := by
    simp only [orPrefix, liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    apply PrefixEnsures.bind ha
    intro yes
    split
    · exact PrefixPreserves.pure c.safe _
    · exact hb
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold consumeDataDonePrefix rxBranch
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head setPeerEndpointPrefix; exact ProductAmbientContracts.drop (setPeerEndpointPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head receivedWithKeypairPrefix; exact receivedWithKeypairPrefix_preserves_product c t.put _ _)
    | (maintenance_head timersHandshakeCompletePrefix; exact ProductAmbientContracts.drop (timersHandshakeCompletePrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c t _)
    | (maintenance_head keepKeyFreshRxPrefix; exact keepKeyFreshRxPrefix_preserves_product c hq _)
    | (maintenance_head timersAnyAuthenticatedPacketReceivedPrefix; exact ProductAmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head timersTraversalPrefix; exact ProductAmbientContracts.drop (timersTraversalPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head updateRxStatsPrefix; exact updateRxStatsPrefix_preserves_product c r _ _)
    | (maintenance_head timersDataReceivedPrefix; exact ProductAmbientContracts.drop (timersDataReceivedPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head lookupSrcPrefix; exact ProductAmbientContracts.drop (lookupSrcPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_lift_action_head dishonest; exact r.dishonest _)
    | (maintenance_lift_action_head inetEcnDecapsulate; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (inetEcnDecapsulate_sameWGStore _ _ _)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head andPrefix; apply and_ok)
    | (maintenance_head orPrefix; apply or_ok)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | (maintenance_head ite; first | apply lifted_conditional | apply conditional)
    | maintenance_intro
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

end Leanux.Proofs.WG.Lifetimes
