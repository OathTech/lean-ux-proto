import Leanux.Proofs.WG.Packets.AddressShape
import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.WG.Lifetimes.DeviceXmit

/-! Literal original source factors at the routing query and staged append.
The input/output World equations below keep the query attached to its actual
caller prefix. They do not assert initialized reachability or key ownership. -/
namespace Leanux.Proofs.WG.Packets
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.CounterWindow

structure RxReady where
  protocol : Nat
  bytes : List UInt8
  ipLen : Nat
  originalLen : Nat

def rxPrepare (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : M (Option RxReady) := do
  setPeerEndpoint pid endpoint
  if ← branch .doneReceivedNew (← receivedWithKeypair pid pkt.keypair) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : M (Option RxReady) := do
    dishonest why   -- then packet_processed: dev_kfree_skb
    return none
  -- a packet with length 0 is a keepalive
  if ← branch .doneRxKeepalive (len == 0) then
    updateRxStats pid MESSAGE_DATA_LEN_0   -- message_data_len(0)
    return none
  timersDataReceived pid
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
  return some ⟨protocol, bytes, ipLen, lenBeforeTrim⟩

def rxAfterLookup (pid : PeerId) (ready : RxReady) (routed : Option PeerId) : M (Option (List UInt8)) := do
  peerPut routed
  if ← branch .doneDishonestPeer (routed != some pid) then
    dishonest .peer
    return none
  updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0)
  return some (ready.bytes.take ready.ipLen)

def rxFinish (pid : PeerId) (ready : RxReady) : M (Option (List UInt8)) := do
  let routed ← lookupSrc ready.protocol ready.bytes
  rxAfterLookup pid ready routed

private theorem bind_if (c : Prop) [Decidable c] (a b : M α) (f : α → M β) :
    (if c then a else b) >>= f = (if c then a >>= f else b >>= f) := by
  split <;> rfl

theorem consumeDataDone_factor (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    consumeDataDone pid pkt endpoint = (do
      let ready ← rxPrepare pid pkt endpoint
      match ready with
      | none => return none
      | some r => rxFinish pid r) := by
  simp only [consumeDataDone, rxPrepare, rxFinish, rxAfterLookup, bind_assoc, bind_if, pure_bind]

private theorem any_spec (a : M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  exact fun _ _ _ _ _ => True.intro

def RxPrepared (pkt : RxPacket) (r : RxReady) : Prop :=
  r.originalLen = pkt.bytes.length ∧ r.protocol = ipTunnelParseProtocol pkt.bytes ∧ ∃ v4 : Bool,
    r.protocol = (if v4 then 4 else 6) ∧
    (if v4 then 20 else 40) ≤ r.ipLen ∧ AddressPreserved v4 pkt.bytes r.bytes

private theorem protocol_length (bytes : List UInt8) (v4 : Bool)
    (h : ipTunnelParseProtocol bytes = (if v4 then 4 else 6)) :
    (if v4 then 20 else 40) ≤ bytes.length := by
  cases v4 <;> unfold ipTunnelParseProtocol at h
  all_goals split at h <;> simp_all
  all_goals split at h <;> simp_all

theorem rxPrepare_shape (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    ⦃fun _ => ⌜True⌝⦄ rxPrepare pid pkt endpoint
    ⦃⇓? result _ => ⌜∀ r, result = some r → RxPrepared pkt r⌝⦄ := by
  have he4 : ⦃fun _ => ⌜ipTunnelParseProtocol pkt.bytes = 4⌝⦄
      inetEcnDecapsulate 4 pkt.ds pkt.bytes
      ⦃⇓? out _ => ⌜AddressPreserved true pkt.bytes out⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    intro w out v hp hr
    exact (hoare_iff_triple _ _ _).mpr
      (inetEcnDecapsulate_address true pkt.ds pkt.bytes (protocol_length pkt.bytes true hp)) w out v True.intro hr
  have he6 : ⦃fun _ => ⌜ipTunnelParseProtocol pkt.bytes = 6⌝⦄
      inetEcnDecapsulate 6 pkt.ds pkt.bytes
      ⦃⇓? out _ => ⌜AddressPreserved false pkt.bytes out⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    intro w out v hp hr
    exact (hoare_iff_triple _ _ _).mpr
      (inetEcnDecapsulate_address false pkt.ds pkt.bytes (protocol_length pkt.bytes false hp)) w out v True.intro hr
  have hep := any_spec (setPeerEndpoint pid endpoint)
  have hk := any_spec (receivedWithKeypair pid pkt.keypair)
  have hh := any_spec (timersHandshakeComplete pid .walltimeLastHandshakeData)
  have hst := any_spec (sendStagedPackets pid)
  have hf := any_spec (keepKeyFreshRx pid)
  have ha := any_spec (timersAnyAuthenticatedPacketReceived pid)
  have ht := any_spec (timersTraversal pid)
  have hd := any_spec (timersDataReceived pid)
  have hstats := fun len => any_spec (updateRxStats pid len)
  have herr := fun why => any_spec (dishonest why)
  mvcgen [rxPrepare, hep, hk, hh, hst, hf, ha, ht, hd, hstats, herr, he4, he6,
    WG.andM, WG.orM, branch]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [RxPrepared]
  all_goals first
    | (refine ⟨true, ?_, ?_, ?_⟩ <;> simp_all)
    | (refine ⟨false, ?_, ?_, ?_⟩ <;> simp_all)

theorem rxPrepare_routing (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsRoutingCall (rxPrepare pid pkt endpoint) := by
  apply Lifetimes.ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hep := (setPeerEndpoint_routing pid endpoint).wp P
  have hk := (receivedWithKeypair_routing pid pkt.keypair).wp P
  have hh := (timersHandshakeComplete_routing pid .walltimeLastHandshakeData).wp P
  have hst := (sendStagedPackets_routing pid).wp s
  have hf := (keepKeyFreshRx_routing pid).wp s
  have ha := (timersAnyAuthenticatedPacketReceived_routing pid).wp P
  have ht := (timersTraversal_routing pid).wp P
  have hd := (timersDataReceived_routing pid).wp P
  have hstats := fun len => (updateRxStats_routing pid len).wp P
  have herr := fun why => (dishonest_routing why).wp P
  have hecn := fun protocol outer bytes =>
    (routing_kernel _ (Lifetimes.inetEcnDecapsulate_sameKernel protocol outer bytes)).wp P
  mvcgen [rxPrepare, hep, hk, hh, hst, hf, ha, ht, hd, hstats, herr, hecn,
    WG.andM, WG.orM, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem rxAfterLookup_guard (pid : PeerId) (r : RxReady) (routed : Option PeerId) :
    ⦃fun _ => ⌜True⌝⦄ rxAfterLookup pid r routed
    ⦃⇓? result _ => ⌜∀ bytes, result = some bytes →
      routed = some pid ∧ bytes = r.bytes.take r.ipLen⌝⦄ := by
  have hp := any_spec (peerPut routed)
  have hd := any_spec (dishonest .peer)
  have hs := any_spec (updateRxStats pid (r.originalLen + MESSAGE_DATA_LEN_0))
  mvcgen [rxAfterLookup, hp, hd, hs, branch]
  all_goals simp_all

/-- The actual original caller prefix leads to the query's input World, and
the query's output World leads to the original guard/statistics tail. -/
theorem consumeDataDone_query (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (w v : World) (bytes : List UInt8)
    (hr : (consumeDataDone pid pkt endpoint).run w = .ok (some bytes, v)) :
    ∃ r u q,
      (rxPrepare pid pkt endpoint).run w = .ok (some r, u) ∧
      (lookupSrc r.protocol r.bytes).run u = .ok (some pid, q) ∧
      (rxAfterLookup pid r (some pid)).run q = .ok (some bytes, v) ∧
      RxPrepared pkt r ∧ bytes = r.bytes.take r.ipLen := by
  rw [consumeDataDone_factor] at hr
  simp only [StateT.run_bind] at hr
  cases hp : (rxPrepare pid pkt endpoint).run w with
  | error e => simp [hp] at hr
  | ok out =>
    rcases out with ⟨ready, u⟩
    cases ready with
    | none => simp [hp] at hr
    | some r =>
      simp only [hp, except_ok_bind, rxFinish, StateT.run_bind] at hr
      cases hq : (lookupSrc r.protocol r.bytes).run u with
      | error e => simp [hq] at hr
      | ok out =>
        rcases out with ⟨routed, q⟩
        simp only [hq, except_ok_bind] at hr
        have hg := (hoare_iff_triple _ _ _).mpr (rxAfterLookup_guard pid r routed)
          q (some bytes) v True.intro hr bytes rfl
        obtain ⟨rfl, hb⟩ := hg
        exact ⟨r, u, q, rfl, hq, hr,
          (hoare_iff_triple _ _ _).mpr (rxPrepare_shape pid pkt endpoint)
            w (some r) u True.intro hp r rfl, hb⟩

theorem consumeDataDone_authorized (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (w v : World) (bytes : List UInt8) (xs : FlatTable × FlatTable)
    (hi : RoutedView (routingView w) xs)
    (hr : (consumeDataDone pid pkt endpoint).run w = .ok (some bytes, v)) :
    ∃ v4 : Bool, ipTunnelParseProtocol bytes = (if v4 then 4 else 6) ∧
      ipTunnelParseProtocol pkt.bytes = (if v4 then 4 else 6) ∧
      PeerWinner (rootWidth v4) (sourceAddress v4 bytes) (selectedFlat v4 xs) (some pid) ∧
      sourceAddress v4 bytes = sourceAddress v4 pkt.bytes := by
  obtain ⟨r, u, q, hp, hq, _, hs, hb⟩ := consumeDataDone_query pid pkt endpoint w v bytes hr
  obtain ⟨_, hinput, v4, hproto, hlen, haddr⟩ := hs
  have hu := hi.retains (rxPrepare_routing pid pkt endpoint w (some r) u hp)
  rw [hproto] at hq
  have hw := lookupSrc_normal u q xs v4 r.bytes (some pid) hu hq
  have he : sourceAddress v4 bytes = sourceAddress v4 r.bytes := by
    rw [hb]
    exact sourceAddress_take v4 r.bytes r.ipLen hlen
  refine ⟨v4, ?_, hinput.symm.trans hproto, he ▸ hw, he.trans haddr.2.2⟩
  rw [hb]
  exact protocol_after_trim v4 pkt.bytes r.bytes r.ipLen (hinput.symm.trans hproto) haddr hlen

def destinationField (family : Nat) (bytes : List UInt8) : Nat :=
  if family == 4 then beAt bytes 16 4 else beAt bytes 24 16

def txHeaders (family addr : Nat) (pkts : List Packet) : M Unit :=
  forIn pkts () fun p _ => do
    if destinationField family p.bytes != addr then
      invariant "the environment's destination disagrees with the packet header"
    return .yield ()

theorem txHeaders_spec (family addr : Nat) (pkts : List Packet) :
    ⦃fun _ => ⌜True⌝⦄ txHeaders family addr pkts
    ⦃⇓? _ _ => ⌜∀ p ∈ pkts, destinationField family p.bytes = addr⌝⦄ := by
  induction pkts with
  | nil => simp only [txHeaders, List.forIn_nil]; mvcgen; simp
  | cons p ps ih =>
    simp only [txHeaders, List.forIn_cons] at *
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, ih, invariant]
    all_goals simp_all

def txWalk (pkts : List Packet) (mtu : Nat) (acc : List Packet) : M (List Packet) :=
  forIn pkts acc fun pkt packets => do
    _ ← branch .xmitWalk true
    _ ← branch .xmitShareFailed false
    return .yield (packets ++ [{pkt with mtu}])

theorem txWalk_spec (pkts : List Packet) (mtu : Nat) (acc : List Packet) :
    ⦃fun _ => ⌜True⌝⦄ txWalk pkts mtu acc
    ⦃⇓? packets _ => ⌜packets = acc ++ pkts.map (fun pkt => {pkt with mtu})⌝⦄ := by
  induction pkts generalizing acc with
  | nil => simp only [txWalk, List.forIn_nil]; mvcgen; simp
  | cons p ps ih =>
    simp only [txWalk, List.forIn_cons] at *
    mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, ih, branch]
    all_goals simp_all [List.append_assoc]

def txCheck (family addr : Nat) (pkts : List Packet) (mtu : Nat) : M Bool := do
  let some first := pkts.head? | invariant "wg_xmit without a packet"
  let realProtocol := match first.bytes with
    | b :: _ => if b.toNat / 16 == 4 then ETH_P_IP else if b.toNat / 16 == 6 then ETH_P_IPV6 else 0
    | [] => 0
  let skbProtocol := if family == 4 then ETH_P_IP else ETH_P_IPV6
  -- `real_protocol && skb->protocol == real_protocol`
  let ok ← WG.andM (branch .checkProtoParsed (realProtocol != 0))
    (branch .checkProtoMatches (skbProtocol == realProtocol))
  if ← branch .xmitBadProtocol !ok then
    modifyDev fun d => {d with txErrors := d.txErrors + 1}
    return false
  txHeaders family addr pkts
  return true

def txError (family : Nat) (ret : Int) : M Int := do
  -- err_icmp: icmp_ndo_send / icmpv6_ndo_send (cut points, whose rate limit
  -- and IP output draw cut-site choices), then err. The error is sent iff
  -- the rate limits allowed it, and then `icmp_global_consume` drew
  -- (icmp.c:310-339, ipv6/icmp.c:195-238: type 3 / type 1 is in the
  -- default ratemask, wg0 is not loopback, the reply's route is local);
  -- the ICMP's loopback delivery raises NET_RX, whose section runs at
  -- `__dev_queue_xmit`'s `rcu_read_unlock_bh` (`loopbackSend`).
  if !(← branch .xmitErrorInet (family == 4)) then _ ← branch .xmitErrorInet6 (family == 6)
  let drawn ← skipCutSites ([.icmpCredit, .ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts)
  loopbackSend [] (drawn.contains (HiddenSite.icmpCredit).info.id)
  modifyDev fun d => { d with txErrors := d.txErrors + 1 }   -- DEV_STATS_INC(dev, tx_errors)
  return ret

def txSelect (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) : M (Except Int (PeerId × List Packet)) := do
  if ← branch .xmitNoPeer peer.isNone then
    if !(← branch .xmitNoPeerInet (family == 4)) then _ ← branch .xmitNoPeerInet6 (family == 6)
    return .error (← txError family (-ENOKEY))
  let some pid := peer | invariant "unreachable"
  let epFamily := (← getPeer pid).endpoint.map (·.family) |>.getD 0
  if ← WG.andM (branch .xmitEndpointNotInet (epFamily != AF_INET)) (branch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
    peerPut peer   -- err_peer
    return .error (← txError family (-EDESTADDRREQ))
  _ ← branch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
  -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
  if !(← branch .xmitNotGso (pkts.length < 2)) then
    -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
    -- an allocation inside skb_segment fails (A's domain, `envOk`)
    if ← branch .xmitGsoError !(← envOk .skbSegment) then
      peerPut peer   -- err_peer
      return .error (← txError family (-ENOMEM))
  -- skb_list_walk_safe (device.c:189-204): every packet of the list gets
  -- the one `mtu` of this call
  let packets ← txWalk pkts mtu []
  _ ← branch .xmitWalk false
  -- `while (skb_queue_len(&peer->staged_packet_queue) > MAX_STAGED_PACKETS)`
  -- (device.c:211-214): the oldest packets go, one `tx_dropped` each, before
  -- the new ones are spliced (W4: the trim)
  Lifetimes.xmitTrim pid
  return .ok (pid, packets)

def txFinish (pid : PeerId) (packets : List Packet) : M Int := do
  Lifetimes.xmitSplice pid packets
  sendStagedPackets pid
  peerPut (some pid)
  return 0

theorem txCheck_valid (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ⦃fun _ => ⌜True⌝⦄ txCheck family addr pkts mtu
    ⦃⇓? ok _ => ⌜ok = true → pkts ≠ [] ∧ ∀ p ∈ pkts, destinationField family p.bytes = addr⌝⦄ := by
  have hh := txHeaders_spec family addr pkts
  have he := any_spec (modifyDev fun d => {d with txErrors := d.txErrors + 1})
  mvcgen [txCheck, hh, he, branch, WG.andM, invariant]
  all_goals simp_all
  all_goals intro hempty; subst pkts; simp_all

theorem txCheck_routing (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    SameView routingView (txCheck family addr pkts mtu) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have he := (modifyDev_routing (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    txCheck, txHeaders, he, branch, WG.andM, invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals simp_all [P]

theorem txError_spec (family : Nat) (ret : Int) :
    ⦃fun _ => ⌜True⌝⦄ txError family ret ⦃⇓? result _ => ⌜result = ret⌝⦄ := by
  have hc := fun sites => any_spec (skipCutSites sites)
  have hl := fun raised => any_spec (loopbackSend [] raised)
  have he := any_spec (modifyDev fun d => {d with txErrors := d.txErrors + 1})
  mvcgen [txError, hc, hl, he, branch]

def TxSelected (peer : Option PeerId) (pkts : List Packet) (mtu : Nat)
    (result : Except Int (PeerId × List Packet)) : Prop :=
  match result with
  | .error err => err ≠ 0
  | .ok (pid, packets) => peer = some pid ∧ packets = pkts.map (fun pkt => {pkt with mtu})

theorem txSelect_spec (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) :
    ⦃fun _ => ⌜True⌝⦄ txSelect family pkts mtu peer
    ⦃⇓? result _ => ⌜TxSelected peer pkts mtu result⌝⦄ := by
  have he := txError_spec family
  have hp := fun peer => any_spec (peerPut peer)
  have hg := fun pid => any_spec (getPeer pid)
  have ht := fun pid => any_spec (Lifetimes.xmitTrim pid)
  have ha := any_spec (envOk .skbSegment)
  have hw := txWalk_spec pkts mtu []
  mvcgen [txSelect, he, hp, hg, ht, ha, hw, branch, WG.andM, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TxSelected, ENOKEY, EDESTADDRREQ, ENOMEM]

private theorem bind_option (o : Option α) (a : α → M β) (b : M β) (f : β → M γ) :
    (match o with | some v => a v | none => b) >>= f =
      match o with | some v => a v >>= f | none => b >>= f := by
  cases o <;> rfl

private theorem invariant_bind (msg : String) (f : α → M β) :
    invariant msg >>= f = invariant msg := rfl

private theorem bind_congr (a : M α) (f g : α → M β) (h : ∀ x, f x = g x) :
    a >>= f = a >>= g := congrArg (fun f => a >>= f) (funext h)

theorem wgXmit_factor (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    wgXmit family addr pkts mtu = (do
      if !(← txCheck family addr pkts mtu) then return -EPROTONOSUPPORT
      let peer ← lookupDst family addr
      match ← txSelect family pkts mtu peer with
      | .error err => return err
      | .ok (pid, packets) => txFinish pid packets) := by
  rw [Lifetimes.wgXmitSource_eq]
  cases hh : pkts.head? <;> simp only [Lifetimes.wgXmitSource, txCheck, txError, txSelect, txFinish, txHeaders, txWalk, destinationField, beAt,
    bind_assoc, bind_if, bind_option, invariant_bind, pure_bind, hh]
  all_goals repeat' first
    | rfl
    | apply bind_congr
    | intro_forall
    | (split <;> try simp_all only [bind_assoc, bind_if, bind_option, invariant_bind,
        pure_bind, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true])
    | simp only [bind_assoc, bind_if, bind_option, invariant_bind, pure_bind,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]

/-- Exact original-call chain ending at the completed staged append. The following
send/put tail is retained; this is not a later encryption or wire-send claim. -/
def TxHandoff (family addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w v : World) (pid : PeerId) : Prop :=
  ∃ u q r s,
    (txCheck family addr pkts mtu).run w = .ok (true, u) ∧
    (lookupDst family addr).run u = .ok (some pid, q) ∧
    (txSelect family pkts mtu (some pid)).run q =
      .ok (.ok (pid, pkts.map (fun pkt => {pkt with mtu})), r) ∧
    (Lifetimes.xmitSplice pid (pkts.map (fun pkt => {pkt with mtu}))).run r = .ok ((), s) ∧
    (do sendStagedPackets pid; peerPut (some pid); pure (0 : Int)).run s = .ok (0, v)

theorem wgXmit_handoff (family addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w v : World) (hr : (wgXmit family addr pkts mtu).run w = .ok (0, v)) :
    ∃ pid, TxHandoff family addr pkts mtu w v pid := by
  rw [wgXmit_factor] at hr
  simp only [StateT.run_bind] at hr
  cases hc : (txCheck family addr pkts mtu).run w with
  | error e => simp [hc] at hr
  | ok out =>
    rcases out with ⟨ok, u⟩
    cases ok with
    | false => simp [hc, EPROTONOSUPPORT] at hr
    | true =>
      simp only [hc, except_ok_bind, Bool.not_true, Bool.false_eq_true, if_false] at hr
      simp only [StateT.run_bind] at hr
      cases hq : (lookupDst family addr).run u with
      | error e => simp [hq] at hr
      | ok out =>
        rcases out with ⟨peer, q⟩
        simp only [hq, except_ok_bind, StateT.run_bind] at hr
        cases hs : (txSelect family pkts mtu peer).run q with
        | error e => simp [hs] at hr
        | ok out =>
          rcases out with ⟨selected, r⟩
          have hv := (hoare_iff_triple _ _ _).mpr (txSelect_spec family pkts mtu peer)
            q selected r True.intro hs
          cases selected with
          | error err =>
            simp only [hs, except_ok_bind, StateT.run_pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
            change (Except.ok (err, r) : Except Stop (Int × World)) = .ok (0, v) at hr
            exact False.elim (hv (congrArg Prod.fst (Except.ok.inj hr)))
          | ok pair =>
            rcases pair with ⟨pid, packets⟩
            obtain ⟨rfl, rfl⟩ := hv
            simp only [hs, except_ok_bind, txFinish, StateT.run_bind] at hr
            cases hh : (Lifetimes.xmitSplice pid (pkts.map (fun pkt => {pkt with mtu}))).run r with
            | error e => simp [hh] at hr
            | ok out =>
              rcases out with ⟨⟨⟩, s⟩
              simp only [hh, except_ok_bind] at hr
              exact ⟨pid, u, q, r, s, hc, hq, hs, hh, hr⟩

theorem destinationField_bound (v4 : Bool) (bytes : List UInt8) :
    destinationField (if v4 then 4 else 6) bytes < 2 ^ rootWidth v4 := by
  cases v4
  · exact beAt_bound bytes 24 16
  · exact beAt_bound bytes 16 4

theorem wgXmit_authorized (v4 : Bool) (addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w v : World) (xs : FlatTable × FlatTable) (hi : RoutedView (routingView w) xs)
    (hr : (wgXmit (if v4 then 4 else 6) addr pkts mtu).run w = .ok (0, v)) :
    ∃ pid, TxHandoff (if v4 then 4 else 6) addr pkts mtu w v pid ∧
      PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) (some pid) ∧
      ∀ pkt ∈ pkts, destinationField (if v4 then 4 else 6) pkt.bytes = addr := by
  obtain ⟨pid, hh⟩ := wgXmit_handoff _ addr pkts mtu w v hr
  have hkeep := hh
  obtain ⟨u, q, r, s, hc, hq, _, _, _⟩ := hh
  have hv := (hoare_iff_triple _ _ _).mpr (txCheck_valid _ addr pkts mtu)
    w true u True.intro hc rfl
  have hu : RoutedView (routingView u) xs := by
    rw [txCheck_routing _ addr pkts mtu w true u hc]
    exact hi
  have ha : addr < 2 ^ rootWidth v4 := by
    cases pkts with
    | nil => exact False.elim (hv.1 rfl)
    | cons p ps =>
      rw [← hv.2 p (by simp)]
      exact destinationField_bound v4 p.bytes
  exact ⟨pid, hkeep, lookupDst_normal u q xs v4 addr ha (some pid) hu hq, hv.2⟩

end Leanux.Proofs.WG.Packets
