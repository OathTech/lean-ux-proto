import Leanux.Proofs.WG.Packets.AddressShape
import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.WG.Lifetimes.DeviceXmit

/-! Literal original source factors at the routing query and staged append.
The input/output WGWorld and Ambient equations below keep the query attached to its actual
caller prefix. They do not assert initialized reachability or key ownership. -/
namespace Leanux.Proofs.WG.Packets
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.CounterWindow

structure RxReady where
  protocol : Nat
  bytes : List UInt8
  ipLen : Nat
  originalLen : Nat

def rxPrepare (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : WG.M (Option RxReady) := do
  setPeerEndpoint pid endpoint
  if ← branch .doneReceivedNew (← receivedWithKeypair pid pkt.keypair) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : WG.M (Option RxReady) := do
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

def rxAfterLookup (pid : PeerId) (ready : RxReady) (routed : Option PeerId) : WG.M (Option (List UInt8)) := do
  peerPut routed
  if ← branch .doneDishonestPeer (routed != some pid) then
    dishonest .peer
    return none
  updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0)
  return some (ready.bytes.take ready.ipLen)

def rxFinish (pid : PeerId) (ready : RxReady) : WG.M (Option (List UInt8)) := do
  let routed ← lookupSrc ready.protocol ready.bytes
  rxAfterLookup pid ready routed

private theorem bind_if {m : Type → Type} [Monad m] (c : Prop) [Decidable c] (a b : m α) (f : α → m β) :
    (if c then a else b) >>= f = (if c then a >>= f else b >>= f) := by
  split <;> rfl

theorem consumeDataDone_factor (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    consumeDataDone pid pkt endpoint = (do
      let ready ← rxPrepare pid pkt endpoint
      match ready with
      | none => return none
      | some r => rxFinish pid r) := by
  simp only [consumeDataDone, rxPrepare, rxFinish, rxAfterLookup, bind_assoc, bind_if, pure_bind]

/-- The original arbitrary product action interface, generalized over its state. -/
private theorem any_spec (a : StateT S (Except Stop) α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  exact fun _ _ _ _ _ => True.intro

private theorem any_spec_ambient (a : StateT S AmbientM α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  exact fun _ _ _ _ _ _ _ => True.intro

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

private def rxShapeFinish (pkt : RxPacket) (bytes : List UInt8) (ipLen : Nat) : WG.M (Option RxReady) := do
  if ← branch .doneLenBeyond (ipLen > pkt.bytes.length) then
    dishonest .size
    return none
  if ← branch .doneTrimFailed false then return none
  return some ⟨ipTunnelParseProtocol pkt.bytes, bytes, ipLen, pkt.bytes.length⟩

private def rxShapeParser (pkt : RxPacket) : WG.M (Option RxReady) := do
  if ← branch .doneProtoIp (ipTunnelParseProtocol pkt.bytes == 4) then
    let ipLen := beAt pkt.bytes 2 2
    if ← branch .doneV4TooShort (ipLen < 20) then
      dishonest .size
      return none
    let bytes ← inetEcnDecapsulate 4 pkt.ds pkt.bytes
    rxShapeFinish pkt bytes ipLen
  else if ← branch .doneProtoIpv6 (ipTunnelParseProtocol pkt.bytes == 6) then
    let bytes ← inetEcnDecapsulate 6 pkt.ds pkt.bytes
    rxShapeFinish pkt bytes (beAt pkt.bytes 4 2 + 40)
  else
    dishonest .type
    return none

private theorem rxShapeStep {α β : Type} (a : WG.M α) (f : α → WG.M β)
    (Q : β → WGWorld → Prop) (h : ∀ x, Hoare (f x) (fun _ => True) Q) :
    Hoare (a >>= f) (fun _ => True) Q := hoare_bind _ _ (any_spec_ambient a) h

private theorem rxShapeDecision (d : Decision) (b : Bool) (f : Bool → WG.M α)
    (Q : α → WGWorld → Prop) (h : Hoare (f b) (fun _ => True) Q) :
    Hoare (branch d b >>= f) (fun _ => True) Q := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hp hr
  have hb (g : WGWorld) (a : Ambient) :
      ((branch d b : WG.M Bool).run g).run a = .ok ((b,g), CounterWindow.record a d b) := rfl
  simp only [StateT.run_bind, hb, except_ok_bind] at hr
  exact (hoare_iff_run_ambient _ _ _).mp h w _ result v ambient' hp hr

private theorem rxShapeNone (pkt : RxPacket) :
    Hoare (pure none : WG.M (Option RxReady)) (fun _ => True)
      (fun out _ => ∀ r, out = some r → RxPrepared pkt r) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' _ hr
  cases hr
  simp

private theorem rxShapeFinish_spec (pkt : RxPacket) (v4 : Bool) (bytes : List UInt8) (ipLen : Nat)
    (hproto : ipTunnelParseProtocol pkt.bytes = (if v4 then 4 else 6))
    (hmin : (if v4 then 20 else 40) ≤ ipLen)
    (ha : AddressPreserved v4 pkt.bytes bytes) :
    Hoare (rxShapeFinish pkt bytes ipLen) (fun _ => True)
      (fun out _ => ∀ r, out = some r → RxPrepared pkt r) := by
  unfold rxShapeFinish
  apply rxShapeStep
  intro beyond
  cases beyond with
  | true =>
    apply rxShapeStep
    intro _
    exact rxShapeNone pkt
  | false =>
    apply rxShapeStep
    intro trim
    cases trim with
    | true => exact rxShapeNone pkt
    | false =>
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient result v ambient' _ hr r he
      cases hr
      cases he
      exact ⟨rfl, rfl, v4, hproto, hmin, ha⟩

private theorem rxShapeParser_spec (pkt : RxPacket) :
    Hoare (rxShapeParser pkt) (fun _ => True)
      (fun out _ => ∀ r, out = some r → RxPrepared pkt r) := by
  unfold rxShapeParser
  apply rxShapeDecision
  by_cases h4 : (ipTunnelParseProtocol pkt.bytes == 4) = true
  · simp only [h4, ↓reduceIte]
    apply rxShapeDecision
    by_cases hshort : decide (beAt pkt.bytes 2 2 < 20) = true
    · simp only [hshort, ↓reduceIte]
      apply rxShapeStep
      intro _
      exact rxShapeNone pkt
    · simp only [hshort, Bool.false_eq_true, ↓reduceIte]
      have hproto : ipTunnelParseProtocol pkt.bytes = 4 := by simpa only [beq_iff_eq] using h4
      have hlen := protocol_length pkt.bytes true hproto
      refine hoare_bind _ _ (inetEcnDecapsulate_address true pkt.ds pkt.bytes hlen) ?_
      intro bytes
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient out v ambient' ha hr
      exact (hoare_iff_run_ambient _ _ _).mp
        (rxShapeFinish_spec pkt true bytes _ hproto (by simpa using hshort) ha) _ _ _ _ _ trivial hr
  · simp only [h4, Bool.false_eq_true, ↓reduceIte]
    apply rxShapeDecision
    by_cases h6 : (ipTunnelParseProtocol pkt.bytes == 6) = true
    · simp only [h6, ↓reduceIte]
      have hproto : ipTunnelParseProtocol pkt.bytes = 6 := by simpa only [beq_iff_eq] using h6
      have hlen := protocol_length pkt.bytes false hproto
      refine hoare_bind _ _ (inetEcnDecapsulate_address false pkt.ds pkt.bytes hlen) ?_
      intro bytes
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient out v ambient' ha hr
      exact (hoare_iff_run_ambient _ _ _).mp
        (rxShapeFinish_spec pkt false bytes _ hproto (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) ha) _ _ _ _ _ trivial hr
    · simp only [h6, Bool.false_eq_true, ↓reduceIte]
      apply rxShapeStep
      intro _
      exact rxShapeNone pkt

private def rxShapeInitial (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) : WG.M Unit := do
  setPeerEndpoint pid endpoint
  if ← branch .doneReceivedNew (← receivedWithKeypair pid pkt.keypair) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid

private def rxShapeBody (pid : PeerId) (pkt : RxPacket) : WG.M (Option RxReady) := do
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : WG.M (Option RxReady) := do
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
  rxShapeParser pkt

private theorem rxShapeBody_spec (pid : PeerId) (pkt : RxPacket) :
    Hoare (rxShapeBody pid pkt) (fun _ => True)
      (fun result _ => ∀ r, result = some r → RxPrepared pkt r) := by
  unfold rxShapeBody
  apply rxShapeStep
  intro keepalive
  cases keepalive with
  | true =>
    apply rxShapeStep
    intro _
    exact rxShapeNone pkt
  | false =>
    apply rxShapeStep
    intro _
    apply rxShapeStep
    intro below
    cases below with
    | true =>
      apply rxShapeStep
      intro _
      exact rxShapeNone pkt
    | false =>
      apply rxShapeStep
      intro honest
      cases honest with
      | false =>
        apply rxShapeStep
        intro _
        exact rxShapeNone pkt
      | true => exact rxShapeParser_spec pkt

theorem rxPrepare_shape (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    ⦃fun _ => ⌜True⌝⦄ rxPrepare pid pkt endpoint
    ⦃⇓? result _ => ⌜∀ r, result = some r → RxPrepared pkt r⌝⦄ := by
  have factor : rxPrepare pid pkt endpoint =
      (rxShapeInitial pid pkt endpoint >>= fun _ => rxShapeBody pid pkt) := by
    simp only [rxPrepare, rxShapeInitial, rxShapeBody, rxShapeParser, rxShapeFinish,
      bind_assoc, bind_if]
  rw [factor]
  exact hoare_bind _ _ (any_spec_ambient (rxShapeInitial pid pkt endpoint))
    (fun _ => rxShapeBody_spec pid pkt)

theorem rxPrepare_routing (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsRoutingCall (rxPrepare pid pkt endpoint) := by

  apply Lifetimes.ProjectedAction.of_wp
  intro s
  let P := fun w : WGWorld => RetainsRouting s (routingView w)
  have hep : Preserves P (setPeerEndpoint pid endpoint) :=
    (setPeerEndpoint_routing pid endpoint).wp (RetainsRouting s)
  have hk : Preserves P (receivedWithKeypair pid pkt.keypair) :=
    (receivedWithKeypair_routing pid pkt.keypair).wp (RetainsRouting s)
  have hh : Preserves P (timersHandshakeComplete pid .walltimeLastHandshakeData) :=
    (timersHandshakeComplete_routing pid .walltimeLastHandshakeData).wp (RetainsRouting s)
  have hst : Preserves P (sendStagedPackets pid) := RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have hf : Preserves P (keepKeyFreshRx pid) := RetainsRoutingCall.wp (keepKeyFreshRx_routing pid) s
  have ha : Preserves P (timersAnyAuthenticatedPacketReceived pid) :=
    (timersAnyAuthenticatedPacketReceived_routing pid).wp (RetainsRouting s)
  have ht : Preserves P (timersTraversal pid) := (timersTraversal_routing pid).wp (RetainsRouting s)
  have hd : Preserves P (timersDataReceived pid) := (timersDataReceived_routing pid).wp (RetainsRouting s)
  have hstats (len : Nat) : Preserves P (updateRxStats pid len) :=
    (updateRxStats_routing pid len).wp (RetainsRouting s)
  have herr (why : Dishonest) : Preserves P (dishonest why) :=
    (dishonest_routing why).wp (RetainsRouting s)
  have hecn (protocol outer : Nat) (bytes : List UInt8) : Preserves P (inetEcnDecapsulate protocol outer bytes) :=
    (routing_kernel _ (Lifetimes.inetEcnDecapsulate_sameWGStore protocol outer bytes)).wp (RetainsRouting s)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have keep : Preserves P (rxPrepare pid pkt endpoint) := by
    routing_tx_source [rxPrepare] using [hep, hk, hh, hst, hf, ha, ht, hd, hstats, herr, hecn, ambient]
    all_goals exact hoare_liftAmbient _ P
  exact hoare_consequence keep (fun w h => by
    change RetainsRouting s (routingView w)
    change routingView w = s at h
    rw [h]
    exact RetainsRouting.refl _) (fun _ _ h => h)

theorem rxAfterLookup_guard (pid : PeerId) (r : RxReady) (routed : Option PeerId) :
    ⦃fun _ => ⌜True⌝⦄ rxAfterLookup pid r routed
    ⦃⇓? result _ => ⌜∀ bytes, result = some bytes →
      routed = some pid ∧ bytes = r.bytes.take r.ipLen⌝⦄ := by
  let post := fun (result : Option (List UInt8)) (_ : WGWorld) =>
    ∀ bytes, result = some bytes → routed = some pid ∧ bytes = r.bytes.take r.ipLen
  have step {α : Type} (a : WG.M α) (f : α → WG.M (Option (List UInt8)))
      (hf : ∀ x, Hoare (f x) (fun _ => True) post) :
      Hoare (a >>= f) (fun _ => True) post :=
    hoare_bind _ _ (any_spec_ambient a) hf
  have decision (d : Decision) (b : Bool) (f : Bool → WG.M (Option (List UInt8)))
      (hf : Hoare (f b) (fun _ => True) post) :
      Hoare (branch d b >>= f) (fun _ => True) post := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' _ hr
    have hb (d : Decision) (b : Bool) (g : WGWorld) (a : Ambient) :
        ((branch d b : WG.M Bool).run g).run a = .ok ((b, g), CounterWindow.record a d b) := rfl
    simp only [StateT.run_bind, hb, except_ok_bind] at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ trivial hr
  have done (result : Option (List UInt8)) (h : ∀ bytes, result = some bytes →
      routed = some pid ∧ bytes = r.bytes.take r.ipLen) :
      Hoare (pure result : WG.M _) (fun _ => True) post :=
    hoare_consequence (hoare_pure result (fun _ : WGWorld => True))
      (fun _ h => h) (fun x _ hx => hx.1 ▸ h)
  change Hoare (rxAfterLookup pid r routed) (fun _ => True) post
  unfold rxAfterLookup
  apply step
  intro _
  apply decision
  by_cases hroute : routed = some pid
  · have hb : (routed != some pid) = false := by simp [hroute]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    apply step
    intro _
    apply done
    intro bytes he
    exact ⟨hroute, (Option.some.inj he).symm⟩
  · have hb : (routed != some pid) = true := by simp [hroute]
    simp only [hb, ↓reduceIte]
    apply step
    intro _
    apply done
    intro bytes he
    cases he

/-- The actual caller prefix and guard/statistics tail share both the native
WireGuard state and the reached Ambient endpoint at every cut. -/
theorem consumeDataDone_query (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (w v : WGWorld) (ambient ambient' : Ambient) (bytes : List UInt8)
    (hr : ((consumeDataDone pid pkt endpoint).run w).run ambient = .ok ((some bytes, v), ambient')) :
    ∃ r u q middle afterLookup,
      ((rxPrepare pid pkt endpoint).run w).run ambient = .ok ((some r, u), middle) ∧
      ((lookupSrc r.protocol r.bytes).run u).run middle = .ok ((some pid, q), afterLookup) ∧
      ((rxAfterLookup pid r (some pid)).run q).run afterLookup = .ok ((some bytes, v), ambient') ∧
      RxPrepared pkt r ∧ bytes = r.bytes.take r.ipLen := by
  rw [consumeDataDone_factor] at hr
  simp only [StateT.run_bind] at hr
  cases hp : ((rxPrepare pid pkt endpoint).run w).run ambient with
  | error e => simp [hp] at hr
  | ok out =>
    rcases out with ⟨⟨ready, u⟩, middle⟩
    cases ready with
    | none => simp [hp] at hr
    | some r =>
      simp only [hp, except_ok_bind, rxFinish, StateT.run_bind] at hr
      cases hq : ((lookupSrc r.protocol r.bytes).run u).run middle with
      | error e => simp [hq] at hr
      | ok out =>
        rcases out with ⟨⟨routed, q⟩, afterLookup⟩
        simp only [hq, except_ok_bind] at hr
        have hg := (hoare_iff_run_ambient _ _ _).mp (rxAfterLookup_guard pid r routed)
          q afterLookup (some bytes) v ambient' True.intro hr bytes rfl
        obtain ⟨rfl, hb⟩ := hg
        exact ⟨r, u, q, middle, afterLookup, rfl, hq, hr,
          (hoare_iff_run_ambient _ _ _).mp (rxPrepare_shape pid pkt endpoint)
            w ambient (some r) u middle True.intro hp r rfl, hb⟩

theorem consumeDataDone_authorized (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (w v : WGWorld) (ambient ambient' : Ambient) (bytes : List UInt8) (xs : FlatTable × FlatTable)
    (hi : RoutedView (routingView w) xs)
    (hr : ((consumeDataDone pid pkt endpoint).run w).run ambient = .ok ((some bytes, v), ambient')) :
    ∃ v4 : Bool, ipTunnelParseProtocol bytes = (if v4 then 4 else 6) ∧
      ipTunnelParseProtocol pkt.bytes = (if v4 then 4 else 6) ∧
      PeerWinner (rootWidth v4) (sourceAddress v4 bytes) (selectedFlat v4 xs) (some pid) ∧
      sourceAddress v4 bytes = sourceAddress v4 pkt.bytes := by
  obtain ⟨r, u, q, middle, afterLookup, hp, hq, _, hs, hb⟩ :=
    consumeDataDone_query pid pkt endpoint w v ambient ambient' bytes hr
  obtain ⟨_, hinput, v4, hproto, hlen, haddr⟩ := hs
  have hu := hi.retains ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (rxPrepare_routing pid pkt endpoint) w ambient (some r) u middle hp)
  rw [hproto] at hq
  have hw := lookupSrc_normal u q middle afterLookup xs v4 r.bytes (some pid) hu hq
  have he : sourceAddress v4 bytes = sourceAddress v4 r.bytes := by
    rw [hb]
    exact sourceAddress_take v4 r.bytes r.ipLen hlen
  refine ⟨v4, ?_, hinput.symm.trans hproto, he ▸ hw, he.trans haddr.2.2⟩
  rw [hb]
  exact protocol_after_trim v4 pkt.bytes r.bytes r.ipLen (hinput.symm.trans hproto) haddr hlen

def destinationField (family : Nat) (bytes : List UInt8) : Nat :=
  if family == 4 then beAt bytes 16 4 else beAt bytes 24 16

def txHeaders (family addr : Nat) (pkts : List Packet) : WG.M Unit :=
  forIn pkts () fun p _ => do
    if destinationField family p.bytes != addr then
      invariant "the environment's destination disagrees with the packet header"
    return .yield ()

theorem txHeaders_spec (family addr : Nat) (pkts : List Packet) :
    ⦃fun _ => ⌜True⌝⦄ txHeaders family addr pkts
    ⦃⇓? _ _ => ⌜∀ p ∈ pkts, destinationField family p.bytes = addr⌝⦄ := by

  induction pkts with
  | nil =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' _ hr
    simp
  | cons p ps ih =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' _ hr
    by_cases hp : destinationField family p.bytes = addr
    · simp [txHeaders, List.forIn_cons, hp] at hr
      have tail := (hoare_iff_run_ambient _ _ _).mp ih w ambient result v ambient' trivial (by simpa [txHeaders] using hr)
      simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hp tail
    · simp [txHeaders, List.forIn_cons, hp, invariant, AmbientM.invariant] at hr
      cases hr

def txWalk (pkts : List Packet) (mtu : Nat) (acc : List Packet) : WG.M (List Packet) :=
  forIn pkts acc fun pkt packets => do
    _ ← branch .xmitWalk true
    _ ← branch .xmitShareFailed false
    return .yield (packets ++ [{pkt with mtu}])

theorem txWalk_spec (pkts : List Packet) (mtu : Nat) (acc : List Packet) :
    ⦃fun _ => ⌜True⌝⦄ txWalk pkts mtu acc
    ⦃⇓? packets _ => ⌜packets = acc ++ pkts.map (fun pkt => {pkt with mtu})⌝⦄ := by

  induction pkts generalizing acc with
  | nil =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient packets v ambient' _ hr
    simp [txWalk] at hr
    simp [hr.1.1]
  | cons p ps ih =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient packets v ambient' _ hr
    simp [txWalk, List.forIn_cons, branch, AmbientM.branch] at hr
    have tail := (hoare_iff_run_ambient _ _ _).mp
      (ih (acc ++ [{p with mtu}])) w _ packets v ambient' trivial
      (by simpa [txWalk, branch, AmbientM.branch] using hr)
    simpa [List.append_assoc] using tail

def txCheck (family addr : Nat) (pkts : List Packet) (_mtu : Nat) : WG.M Bool := do
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

def txError (family : Nat) (first : Packet) (ret : Int) : WG.M Int := do
  -- The credit draw is followed by the IPv4 source route and address
  -- classification. A route error suppresses the loopback delivery.
  if !(← branch .xmitErrorInet (family == 4)) then _ ← branch .xmitErrorInet6 (family == 6)
  let drawn ← skipCutSites ([.icmpCredit, .ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts)
  let mut sent := drawn.contains (HiddenSite.icmpCredit).info.id
  if family == 4 && sent then
    let src := ((first.bytes.drop 12).take 4).foldl (fun acc b => acc * 256 + b.toNat) 0
    match ← Net.routeOutput4 0 src with
    | .error _ => sent := false
    | .ok _ =>
      _ ← Net.Fib.inetDevAddrType (some WG0_IFINDEX) src
      Net.neighbourClassify LO_IFINDEX
  loopbackSend [] sent
  modifyDev fun d => { d with txErrors := d.txErrors + 1 }   -- DEV_STATS_INC(dev, tx_errors)
  return ret

def txSelect (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) : WG.M (Except Int (PeerId × List Packet)) := do
  if ← branch .xmitNoPeer peer.isNone then
    if !(← branch .xmitNoPeerInet (family == 4)) then _ ← branch .xmitNoPeerInet6 (family == 6)
    return .error (← txError family (pkts.head?.getD {bytes := []}) (-ENOKEY))
  let some pid := peer | invariant "unreachable"
  let epFamily := (← getPeer pid).endpoint.map (·.family) |>.getD 0
  if ← WG.andM (branch .xmitEndpointNotInet (epFamily != AF_INET)) (branch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
    peerPut peer   -- err_peer
    return .error (← txError family (pkts.head?.getD {bytes := []}) (-EDESTADDRREQ))
  _ ← branch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
  -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
  if !(← branch .xmitNotGso (pkts.length < 2)) then
    -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
    -- an allocation inside skb_segment fails (A's domain, `envOk`)
    if ← branch .xmitGsoError !(← envOk .skbSegment) then
      peerPut peer   -- err_peer
      return .error (← txError family (pkts.head?.getD {bytes := []}) (-ENOMEM))
  -- skb_list_walk_safe (device.c:189-204): every packet of the list gets
  -- the one `mtu` of this call
  let packets ← txWalk pkts mtu []
  _ ← branch .xmitWalk false
  -- `while (skb_queue_len(&peer->staged_packet_queue) > MAX_STAGED_PACKETS)`
  -- (device.c:211-214): the oldest packets go, one `tx_dropped` each, before
  -- the new ones are spliced (W4: the trim)
  Lifetimes.xmitTrim pid
  return .ok (pid, packets)

def txFinish (pid : PeerId) (packets : List Packet) : WG.M Int := do
  Lifetimes.xmitSplice pid packets
  sendStagedPackets pid
  peerPut (some pid)
  return 0

theorem txCheck_valid (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ⦃fun _ => ⌜True⌝⦄ txCheck family addr pkts mtu
    ⦃⇓? ok _ => ⌜ok = true → pkts ≠ [] ∧ ∀ p ∈ pkts, destinationField family p.bytes = addr⌝⦄ := by

  cases pkts with
  | nil =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' _ hr
    simp [txCheck, invariant, AmbientM.invariant] at hr
    cases hr
  | cons first rest =>
    simp only [txCheck, List.head?_cons]
    refine hoare_bind _ _ (any_spec_ambient _) ?_
    intro parsed
    refine hoare_bind _ _ (any_spec_ambient _) ?_
    intro bad
    cases bad with
    | false =>
      refine hoare_bind _ _ (txHeaders_spec family addr (first :: rest)) ?_
      intro result
      apply hoare_consequence (hoare_pure true _) (fun _ h => h)
      intro ok w h _
      exact ⟨List.cons_ne_nil _ _, h.2⟩
    | true =>
      refine hoare_bind _ _ (any_spec_ambient _) ?_
      intro result
      apply hoare_consequence (hoare_pure false _) (fun _ h => h)
      intro ok w h he
      simp [h.1] at he

theorem txCheck_routing (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    SameView routingView (txCheck family addr pkts mtu) := by

  apply SameView.of_wp
  intro s
  let P := fun w : WGWorld => routingView w = s
  have he : Preserves P (modifyDev fun d => {d with txErrors := d.txErrors + 1}) :=
    (modifyDev_routing (fun d => {d with txErrors := d.txErrors + 1}) (fun _ => rfl)).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  change Preserves P (txCheck family addr pkts mtu)
  routing_tx_source [txCheck, txHeaders] using [he, ambient]
  all_goals exact hoare_liftAmbient _ P

theorem txError_spec (family : Nat) (first : Packet) (ret : Int) :
    ⦃fun _ => ⌜True⌝⦄ txError family first ret ⦃⇓? result _ => ⌜result = ret⌝⦄ := by

  let post := fun result (_ : WGWorld) => result = ret
  have step {α : Type} (a : WG.M α) (f : α → WG.M Int)
      (hf : ∀ x, Hoare (f x) (fun _ => True) post) :
      Hoare (a >>= f) (fun _ => True) post :=
    hoare_bind _ _ (any_spec_ambient a) hf
  have done : Hoare (pure ret : WG.M Int) (fun _ => True) post :=
    hoare_consequence (hoare_pure ret (fun _ : WGWorld => True))
      (fun _ h => h) (fun _ _ h => h.1)
  change Hoare (txError family first ret) (fun _ => True) post
  unfold txError
  repeat' first
    | (packet_hoare_head Bind.bind; apply step; intro)
    | (packet_hoare_head Pure.pure; exact done)
    | (packet_hoare_head ite; split)
    | simp only
    | split

def TxSelected (peer : Option PeerId) (pkts : List Packet) (mtu : Nat)
    (result : Except Int (PeerId × List Packet)) : Prop :=
  match result with
  | .error err => err ≠ 0
  | .ok (pid, packets) => peer = some pid ∧ packets = pkts.map (fun pkt => {pkt with mtu})

theorem txSelect_spec (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) :
    ⦃fun _ => ⌜True⌝⦄ txSelect family pkts mtu peer
    ⦃⇓? result _ => ⌜TxSelected peer pkts mtu result⌝⦄ := by

  let post := fun result (_ : WGWorld) => TxSelected peer pkts mtu result
  have step {α : Type} (a : WG.M α) (f : α → WG.M (Except Int (PeerId × List Packet)))
      (hf : ∀ x, Hoare (f x) (fun _ => True) post) :
      Hoare (a >>= f) (fun _ => True) post :=
    hoare_bind _ _ (any_spec_ambient a) hf
  have decision (d : Decision) (b : Bool)
      (f : Bool → WG.M (Except Int (PeerId × List Packet)))
      (hf : Hoare (f b) (fun _ => True) post) :
      Hoare (branch d b >>= f) (fun _ => True) post := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' _ hr
    have hb (d : Decision) (b : Bool) (g : WGWorld) (a : Ambient) :
        ((branch d b : WG.M Bool).run g).run a = .ok ((b, g), CounterWindow.record a d b) := rfl
    simp only [StateT.run_bind, hb, except_ok_bind] at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ trivial hr
  have error (ret : Int) (hne : ret ≠ 0) :
      Hoare (do
        let result ← txError family (pkts.head?.getD {bytes := []}) ret
        pure (Except.error result : Except Int (PeerId × List Packet)))
      (fun _ => True) post := by
    refine hoare_bind _ _ (txError_spec family (pkts.head?.getD {bytes := []}) ret) ?_
    intro result
    apply hoare_consequence (hoare_pure (.error result : Except Int (PeerId × List Packet)) _)
      (fun _ h => h)
    intro x w h
    rcases h with ⟨rfl, rfl⟩
    exact hne
  have walk (f : List Packet → WG.M (Except Int (PeerId × List Packet)))
      (hf : Hoare (f (pkts.map (fun pkt => {pkt with mtu}))) (fun _ => True) post) :
      Hoare (txWalk pkts mtu [] >>= f) (fun _ => True) post := by
    refine hoare_bind _ _ (txWalk_spec pkts mtu []) ?_
    intro packets
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hp hr
    simp only [List.nil_append] at hp
    subst packets
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ trivial hr
  have done (result : Except Int (PeerId × List Packet)) (h : TxSelected peer pkts mtu result) :
      Hoare (pure result : WG.M _) (fun _ => True) post :=
    hoare_consequence (hoare_pure result (fun _ : WGWorld => True))
      (fun _ h => h) (fun x _ hx => hx.1 ▸ h)
  have conditional (p : Prop) [Decidable p] (a b : WG.M (Except Int (PeerId × List Packet)))
      (ha : p → Hoare a (fun _ => True) post) (hb : ¬p → Hoare b (fun _ => True) post) :
      Hoare (if p then a else b) (fun _ => True) post := by
    by_cases hp : p
    · simpa only [ite_eq_left hp] using ha hp
    · simpa only [ite_eq_right hp] using hb hp
  change Hoare (txSelect family pkts mtu peer) (fun _ => True) post
  cases peer <;> unfold txSelect WG.andM
  all_goals simp only [Option.isNone_none, Option.isNone_some, bind_assoc, bind_if, pure_bind]
  all_goals repeat' first
    | contradiction
    | (packet_bind_head txError
       first
       | exact error (-ENOKEY) (by decide)
       | exact error (-EDESTADDRREQ) (by decide)
       | exact error (-ENOMEM) (by decide))
    | (packet_bind_head txWalk; apply walk)
    | (packet_bind_head branch; apply decision)
    | (packet_hoare_head Bind.bind; apply step; intro)
    | (packet_hoare_head Pure.pure; apply done; simp [TxSelected])
    | (packet_hoare_head ite; apply conditional; all_goals intro h)
    | simp only

private theorem bind_option {m : Type → Type} [Monad m]
    (o : Option α) (a : α → m β) (b : m β) (f : β → m γ) :
    (match o with | some v => a v | none => b) >>= f =
      match o with | some v => a v >>= f | none => b >>= f := by
  cases o <;> rfl

private theorem invariant_bind (msg : String) (f : α → Leanux.M β) :
    invariant msg >>= f = invariant msg := rfl

private theorem invariant_bind_ambient (msg : String) (f : α → WG.M β) :
    invariant msg >>= f = invariant msg := rfl

private theorem bind_congr {m : Type → Type} [Monad m]
    (a : m α) (f g : α → m β) (h : ∀ x, f x = g x) :
    a >>= f = a >>= g := congrArg (fun f => a >>= f) (funext h)

theorem wgXmit_factor (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    wgXmit family addr pkts mtu = (do
      if !(← txCheck family addr pkts mtu) then return -EPROTONOSUPPORT
      let peer ← lookupDst family addr
      match ← txSelect family pkts mtu peer with
      | .error err => return err
      | .ok (pid, packets) => txFinish pid packets) := by
  rw [Lifetimes.wgXmitSource_eq]
  cases hh : pkts.head? with
  | none =>
    simp only [Lifetimes.wgXmitSource, txCheck, hh, invariant_bind_ambient]
  | some first =>
    conv => lhs; unfold Lifetimes.wgXmitSource; rw [hh]
    change (do
      let realProtocol := match first.bytes with
        | b :: _ => if b.toNat / 16 == 4 then ETH_P_IP else if b.toNat / 16 == 6 then ETH_P_IPV6 else 0
        | [] => 0
      let skbProtocol := if family == 4 then ETH_P_IP else ETH_P_IPV6
      -- `real_protocol && skb->protocol == real_protocol`
      let ok ← WG.andM (branch .checkProtoParsed (realProtocol != 0))
        (branch .checkProtoMatches (skbProtocol == realProtocol))
      if ← branch .xmitBadProtocol !ok then
        modifyDev fun d => {d with txErrors := d.txErrors + 1}
        return -EPROTONOSUPPORT
      txHeaders family addr pkts
      let peer ← lookupDst family addr
      if ← branch .xmitNoPeer peer.isNone then
        if !(← branch .xmitNoPeerInet (family == 4)) then _ ← branch .xmitNoPeerInet6 (family == 6)
        return ← txError family first (-ENOKEY)
      let some pid := peer | invariant "unreachable"
      let epFamily := (← getPeer pid).endpoint.map (·.family) |>.getD 0
      if ← WG.andM (branch .xmitEndpointNotInet (epFamily != AF_INET)) (branch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
        peerPut peer   -- err_peer
        return ← txError family first (-EDESTADDRREQ)
      _ ← branch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
      -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
      if !(← branch .xmitNotGso (pkts.length < 2)) then
        -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
        -- an allocation inside skb_segment fails (A's domain, `envOk`)
        if ← branch .xmitGsoError !(← envOk .skbSegment) then
          peerPut peer   -- err_peer
          return ← txError family first (-ENOMEM)
      -- skb_list_walk_safe (device.c:189-204): every packet of the list gets
      -- the one `mtu` of this call
      let packets ← txWalk pkts mtu []
      _ ← branch .xmitWalk false
      -- `while (skb_queue_len(&peer->staged_packet_queue) > MAX_STAGED_PACKETS)`
      -- (device.c:211-214): the oldest packets go, one `tx_dropped` each, before
      -- the new ones are spliced (W4: the trim)
      Lifetimes.xmitTrim pid
      Lifetimes.xmitSplice pid packets
      sendStagedPackets pid
      peerPut peer
      return 0   -- NETDEV_TX_OK
      : WG.M Int) = _
    simp only [txCheck, txSelect, txFinish, hh, Option.getD_some,
      bind_assoc, bind_if, pure_bind]
    all_goals repeat' first
      | rfl
      | apply bind_congr
      | keypairs_intro_forall
      | (split <;> try simp_all only [bind_assoc, bind_if,
          invariant_bind_ambient, pure_bind, bind_pure, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true])
      | simp only [bind_assoc, bind_if, bind_option,
          invariant_bind_ambient, pure_bind, bind_pure, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ite_false, ite_true]

/-- Exact original-call chain ending at the completed staged append. The following
send/put tail is retained; this is not a later encryption or wire-send claim. -/
def TxHandoff (family addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w v : WGWorld) (ambient ambient' : Ambient) (pid : PeerId) : Prop :=
  ∃ u q r s a b c d,
    ((txCheck family addr pkts mtu).run w).run ambient = .ok ((true, u), a) ∧
    ((lookupDst family addr).run u).run a = .ok ((some pid, q), b) ∧
    ((txSelect family pkts mtu (some pid)).run q).run b =
      .ok ((.ok (pid, pkts.map (fun pkt => {pkt with mtu})), r), c) ∧
    ((Lifetimes.xmitSplice pid (pkts.map (fun pkt => {pkt with mtu}))).run r).run c = .ok (((), s), d) ∧
    ((do sendStagedPackets pid; peerPut (some pid); pure (0 : Int) : WG.M Int).run s).run d =
      .ok ((0, v), ambient')

theorem wgXmit_handoff (family addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((wgXmit family addr pkts mtu).run w).run ambient = .ok ((0, v), ambient')) :
    ∃ pid, TxHandoff family addr pkts mtu w v ambient ambient' pid := by
  rw [wgXmit_factor] at hr
  simp only [StateT.run_bind] at hr
  cases hc : ((txCheck family addr pkts mtu).run w).run ambient with
  | error e => simp [hc] at hr
  | ok out =>
    rcases out with ⟨⟨ok, u⟩, a⟩
    cases ok with
    | false => simp [hc, EPROTONOSUPPORT] at hr
    | true =>
      simp only [hc, except_ok_bind, Bool.not_true, Bool.false_eq_true, ite_false] at hr
      simp only [StateT.run_bind] at hr
      cases hq : ((lookupDst family addr).run u).run a with
      | error e => simp [hq] at hr
      | ok out =>
        rcases out with ⟨⟨peer, q⟩, b⟩
        simp only [hq, except_ok_bind] at hr
        cases hs : ((txSelect family pkts mtu peer).run q).run b with
        | error e => simp [hs] at hr
        | ok out =>
          rcases out with ⟨⟨selected, r⟩, c⟩
          have hv := (hoare_iff_run_ambient _ _ _).mp (txSelect_spec family pkts mtu peer)
            q b selected r c True.intro hs
          cases selected with
          | error err =>
            simp only [hs, except_ok_bind, StateT.run_pure] at hr
            change (Except.ok ((err, r), c) : Except Stop ((Int × WGWorld) × Ambient)) = .ok ((0, v), ambient') at hr
            exact False.elim (hv (congrArg (Prod.fst ∘ Prod.fst) (Except.ok.inj hr)))
          | ok pair =>
            rcases pair with ⟨pid, packets⟩
            obtain ⟨rfl, rfl⟩ := hv
            simp only [hs, except_ok_bind, txFinish, StateT.run_bind] at hr
            cases hh : ((Lifetimes.xmitSplice pid (pkts.map (fun pkt => {pkt with mtu}))).run r).run c with
            | error e => simp [hh] at hr
            | ok out =>
              rcases out with ⟨⟨⟨⟩, s⟩, d⟩
              simp only [hh, except_ok_bind] at hr
              exact ⟨pid, u, q, r, s, a, b, c, d, hc, hq, hs, hh, hr⟩

theorem destinationField_bound (v4 : Bool) (bytes : List UInt8) :
    destinationField (if v4 then 4 else 6) bytes < 2 ^ rootWidth v4 := by
  cases v4
  · exact beAt_bound bytes 24 16
  · exact beAt_bound bytes 16 4

theorem wgXmit_authorized (v4 : Bool) (addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w v : WGWorld) (ambient ambient' : Ambient) (xs : FlatTable × FlatTable)
    (hi : RoutedView (routingView w) xs)
    (hr : ((wgXmit (if v4 then 4 else 6) addr pkts mtu).run w).run ambient = .ok ((0, v), ambient')) :
    ∃ pid, TxHandoff (if v4 then 4 else 6) addr pkts mtu w v ambient ambient' pid ∧
      PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) (some pid) ∧
      ∀ pkt ∈ pkts, destinationField (if v4 then 4 else 6) pkt.bytes = addr := by
  obtain ⟨pid, hh⟩ := wgXmit_handoff _ addr pkts mtu w v ambient ambient' hr
  have hkeep := hh
  obtain ⟨u, q, r, s, a, b, c, d, hc, hq, _, _, _⟩ := hh
  have hv := (hoare_iff_run_ambient _ _ _).mp (txCheck_valid _ addr pkts mtu)
    w ambient true u a True.intro hc rfl
  have hu : RoutedView (routingView u) xs := by
    rw [(Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (txCheck_routing _ addr pkts mtu) w ambient true u a hc]
    exact hi
  have ha : addr < 2 ^ rootWidth v4 := by
    cases pkts with
    | nil => exact False.elim (hv.1 rfl)
    | cons p ps =>
      rw [← hv.2 p (by simp)]
      exact destinationField_bound v4 p.bytes
  exact ⟨pid, hkeep, lookupDst_normal u q a b xs v4 addr ha (some pid) hu hq, hv.2⟩

end Leanux.Proofs.WG.Packets
