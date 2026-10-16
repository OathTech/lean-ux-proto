import Leanux.Proofs.WG.Lifetimes.ReceivePoll
import Leanux.Proofs.WG.Lifetimes.TxCompletion
import Leanux.Proofs.WG.Lifetimes.LoopbackAccess

/-! The complete original transmit entry, including its error/loopback arms,
queue trimming and both getters in the staged-packet splice. The scalar error
counter has an explicit separate contract; packet values acquire store identities
only in the already observed staging caller. -/
set_option maxHeartbeats 800000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

structure WgXmitContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  errors : ∀ P, AmbientSpec I P
    (liftWGPrefix (modifyDev fun d => {d with txErrors := d.txErrors + 1})) (fun _ => P)

structure ProductWgXmitContracts (I : List LifetimeEvent → World → Prop) : Prop where
  errors : ∀ P, ProductAmbientSpec I P
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txErrors := d.txErrors + 1}))) (fun _ => P)

theorem allocationWgXmit : WgXmitContracts AllocationInv where
  errors := by
    intro P
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.safe)
    intro h w ambient x v ambient' hi hr
    have hf : (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
      cases hr
      unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
      simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
      rfl
    have he : identityView v = identityView w := congrArg Prod.fst hf
    exact ⟨hi.1.congr he (congrArg Prod.snd hf), he ▸ hi.2⟩

def xmitTrim (pid : PeerId) : WG.M Unit := do
  for _ in [0:(← getPeer pid).staged.length + 1] do
    let p ← getPeer pid
    if ← branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS) then
      setPeer pid { p with staged := p.staged.drop 1 }
      modifyDev fun d => { d with txDropped := d.txDropped + 1 }
    else break

def xmitTrimPrefix (pid : PeerId) : MixedM Unit := do
  for _ in [0:(← getPeerMixed pid).staged.length + 1] do
    let p ← getPeerMixed pid
    if ← rxBranch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS) then
      setPeerMixed pid { p with staged := p.staged.drop 1 }
      liftWGPrefix (modifyDev fun d => { d with txDropped := d.txDropped + 1 })
    else break

def xmitSplice (pid : PeerId) (packets : List Packet) : WG.M Unit := do
  setPeer pid { (← getPeer pid) with staged := (← getPeer pid).staged ++ packets }

def xmitSplicePrefix (pid : PeerId) (packets : List Packet) : MixedM Unit := do
  setPeerMixed pid { (← getPeerMixed pid) with staged := (← getPeerMixed pid).staged ++ packets }

theorem xmitSplicePrefix_erases (pid : PeerId) (packets : List Packet) :
    ErasesStatePrefix (xmitSplicePrefix pid packets) (xmitSplice pid packets) :=
  erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _))

theorem xmitSplicePrefix_preserves (c : AmbientContracts I) (pid : PeerId) (packets : List Packet) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (xmitSplicePrefix pid packets) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply StatePrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with staged := q.staged ++ packets}

theorem xmitSplicePrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) (packets : List Packet) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (xmitSplicePrefix pid packets)) := by
  unfold xmitSplicePrefix
  simp only [liftWGObserver_bind]
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with staged := q.staged ++ packets}

theorem xmitTrimPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (xmitTrimPrefix pid) (xmitTrim pid) := by
  unfold xmitTrimPrefix xmitTrim rxBranch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match

theorem xmitTrimPrefix_preserves (c : AmbientContracts I) (t : TxContracts I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (xmitTrimPrefix pid) := by
  unfold xmitTrimPrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) pid))
  intro initial
  apply StatePrefixEnsures.bind
  · apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) _ (fun _ h w _ hi => c.safe h w hi)
    intro idx acc
    apply AmbientContracts.drop (Q := fun _ _ => True)
    apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
    intro p
    apply StatePrefixEnsures.bind (c.branch (fun s => True ∧ s.1.slots pid = some p.internalId) _ _)
    intro trim
    split
    · apply StatePrefixEnsures.bind (c.setPeer (fun _ => True) pid {p with staged := p.staged.drop 1})
      intro _
      exact StatePrefixEnsures.bind (t.device (fun _ => True) (.dropped 1))
        (fun _ => c.pure (fun _ => True) _)
    · exact (c.pure (fun s => True ∧ s.1.slots pid = some p.internalId) _).consequence
        (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, True.intro⟩)
  · intro _
    exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)

theorem xmitTrimPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (xmitTrimPrefix pid)) := by
  unfold xmitTrimPrefix rxBranch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', liftWGObserver_bind,
    liftWGObserver_forIn, liftWGObserver_pure]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) pid))
  intro initial
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ c.safe
    intro idx acc
    apply ProductAmbientContracts.drop (Q := fun _ _ => True)
    apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
    intro p
    apply PrefixEnsures.bind (c.branch (fun s => True ∧ s.1.slots pid = some p.internalId) _ _)
    intro trim
    split
    · simp only [liftWGObserver_bind]
      apply PrefixEnsures.bind (c.setPeer (fun _ => True) pid {p with staged := p.staged.drop 1})
      intro _
      exact PrefixEnsures.bind (t.device (fun _ => True) (.dropped 1))
        (fun _ => c.pure (fun _ => True) _)
    · exact (c.pure (fun s => True ∧ s.1.slots pid = some p.internalId) _).consequence
        (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, True.intro⟩)
  · intro _
    exact PrefixPreserves.pure c.safe _

def wgXmitSource (family addr : Nat) (pkts : List Packet) (mtu : Nat) : WG.M Int := do
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
    return -EPROTONOSUPPORT
  for p in pkts do
    let field (off len : Nat) := ((p.bytes.drop off).take len).foldl (fun acc b => acc * 256 + b.toNat) 0
    let dst := if family == 4 then field 16 4 else field 24 16
    if dst != addr then invariant "the environment's destination disagrees with the packet header"
  let err (ret : Int) : WG.M Int := do
    -- err_icmp: icmp_ndo_send / icmpv6_ndo_send (cut points, whose rate limit
    -- and IP output draw cut-site choices), then err. The error is sent iff
    -- the rate limits allowed it, and then `icmp_global_consume` drew
    -- (icmp.c:310-339, ipv6/icmp.c:195-238: type 3 / type 1 is in the
    -- default ratemask, wg0 is not loopback, the reply's route is local);
    -- the ICMP's loopback delivery raises NET_RX, whose section runs at
    -- `__dev_queue_xmit`'s `rcu_read_unlock_bh` (`loopbackSend`).
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
  let peer ← lookupDst family addr
  if ← branch .xmitNoPeer peer.isNone then
    if !(← branch .xmitNoPeerInet (family == 4)) then _ ← branch .xmitNoPeerInet6 (family == 6)
    return ← err (-ENOKEY)
  let some pid := peer | invariant "unreachable"
  let epFamily := (← getPeer pid).endpoint.map (·.family) |>.getD 0
  if ← WG.andM (branch .xmitEndpointNotInet (epFamily != AF_INET)) (branch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
    peerPut peer   -- err_peer
    return ← err (-EDESTADDRREQ)
  _ ← branch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
  -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
  if !(← branch .xmitNotGso (pkts.length < 2)) then
    -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
    -- an allocation inside skb_segment fails (A's domain, `envOk`)
    if ← branch .xmitGsoError !(← envOk .skbSegment) then
      peerPut peer   -- err_peer
      return ← err (-ENOMEM)
  -- skb_list_walk_safe (device.c:189-204): every packet of the list gets
  -- the one `mtu` of this call
  let mut packets : List Packet := []
  for pkt in pkts do
    _ ← branch .xmitWalk true
    _ ← branch .xmitShareFailed false
    packets := packets ++ [{ pkt with mtu }]
  _ ← branch .xmitWalk false
  -- `while (skb_queue_len(&peer->staged_packet_queue) > MAX_STAGED_PACKETS)`
  -- (device.c:211-214): the oldest packets go, one `tx_dropped` each, before
  -- the new ones are spliced (W4: the trim)
  xmitTrim pid
  xmitSplice pid packets
  sendStagedPackets pid
  peerPut peer
  return 0   -- NETDEV_TX_OK

theorem wgXmitSource_eq (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    wgXmit family addr pkts mtu = wgXmitSource family addr pkts mtu := by
  simp only [wgXmit, wgXmitSource, xmitTrim, xmitSplice, bind_assoc, pure_bind]
  congr 1

def wgXmitPrefix (family addr : Nat) (pkts : List Packet) (mtu : Nat) : MixedM Int := do
  let some first := pkts.head? | liftWGPrefix (invariant "wg_xmit without a packet")
  let realProtocol := match first.bytes with
    | b :: _ => if b.toNat / 16 == 4 then ETH_P_IP else if b.toNat / 16 == 6 then ETH_P_IPV6 else 0
    | [] => 0
  let skbProtocol := if family == 4 then ETH_P_IP else ETH_P_IPV6
  -- `real_protocol && skb->protocol == real_protocol`
  let ok ← andPrefix (rxBranch .checkProtoParsed (realProtocol != 0))
    (rxBranch .checkProtoMatches (skbProtocol == realProtocol))
  if ← rxBranch .xmitBadProtocol !ok then
    liftWGPrefix (modifyDev fun d => {d with txErrors := d.txErrors + 1})
    return -EPROTONOSUPPORT
  for p in pkts do
    let field (off len : Nat) := ((p.bytes.drop off).take len).foldl (fun acc b => acc * 256 + b.toNat) 0
    let dst := if family == 4 then field 16 4 else field 24 16
    if dst != addr then liftWGPrefix (invariant "the environment's destination disagrees with the packet header")
  let err (ret : Int) : MixedM Int := do
    -- err_icmp: icmp_ndo_send / icmpv6_ndo_send (cut points, whose rate limit
    -- and IP output draw cut-site choices), then err. The error is sent iff
    -- the rate limits allowed it, and then `icmp_global_consume` drew
    -- (icmp.c:310-339, ipv6/icmp.c:195-238: type 3 / type 1 is in the
    -- default ratemask, wg0 is not loopback, the reply's route is local);
    -- the ICMP's loopback delivery raises NET_RX, whose section runs at
    -- `__dev_queue_xmit`'s `rcu_read_unlock_bh` (`loopbackSend`).
    if !(← rxBranch .xmitErrorInet (family == 4)) then _ ← rxBranch .xmitErrorInet6 (family == 6)
    let drawn ← liftWGPrefix (skipCutSites ([.icmpCredit, .ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts))
    let mut sent := drawn.contains (HiddenSite.icmpCredit).info.id
    if family == 4 && sent then
      let src := ((first.bytes.drop 12).take 4).foldl (fun acc b => acc * 256 + b.toNat) 0
      match ← liftWGPrefix (liftRouting (Net.routeOutput4 0 src)) with
      | .error _ => sent := false
      | .ok _ =>
        _ ← liftWGPrefix (liftRouting (Net.Fib.inetDevAddrType (some WG0_IFINDEX) src))
        liftWGPrefix (liftRouting (Net.neighbourClassify LO_IFINDEX))
    loopbackSendPrefix [] sent
    liftWGPrefix (modifyDev fun d => { d with txErrors := d.txErrors + 1 })   -- DEV_STATS_INC(dev, tx_errors)
    return ret
  let peer ← lookupDstPrefix family addr
  if ← rxBranch .xmitNoPeer peer.isNone then
    if !(← rxBranch .xmitNoPeerInet (family == 4)) then _ ← rxBranch .xmitNoPeerInet6 (family == 6)
    return ← err (-ENOKEY)
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  let epFamily := (← getPeerMixed pid).endpoint.map (·.family) |>.getD 0
  if ← andPrefix (rxBranch .xmitEndpointNotInet (epFamily != AF_INET)) (rxBranch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
    peerPutMixed peer   -- err_peer
    return ← err (-EDESTADDRREQ)
  _ ← rxBranch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
  -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
  if !(← rxBranch .xmitNotGso (pkts.length < 2)) then
    -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
    -- an allocation inside skb_segment fails (A's domain, `envOk`)
    if ← rxBranch .xmitGsoError !(← liftWGPrefix (envOk .skbSegment)) then
      peerPutMixed peer   -- err_peer
      return ← err (-ENOMEM)
  -- skb_list_walk_safe (device.c:189-204): every packet of the list gets
  -- the one `mtu` of this call
  let mut packets : List Packet := []
  for pkt in pkts do
    _ ← rxBranch .xmitWalk true
    _ ← rxBranch .xmitShareFailed false
    packets := packets ++ [{ pkt with mtu }]
  _ ← rxBranch .xmitWalk false
  -- `while (skb_queue_len(&peer->staged_packet_queue) > MAX_STAGED_PACKETS)`
  -- (device.c:211-214): the oldest packets go, one `tx_dropped` each, before
  -- the new ones are spliced (W4: the trim)
  xmitTrimPrefix pid
  xmitSplicePrefix pid packets
  sendStagedPacketsPrefix pid
  peerPutMixed peer
  return 0   -- NETDEV_TX_OK

theorem wgXmitPrefix_erases (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ErasesStatePrefix (wgXmitPrefix family addr pkts mtu) (wgXmit family addr pkts mtu) := by
  rw [wgXmitSource_eq]
  unfold wgXmitPrefix wgXmitSource rxBranch andPrefix WG.andM
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head lookupDstPrefix; exact lookupDstPrefix_erases _ _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_erases _)
    | (maintenance_head xmitTrimPrefix; exact xmitTrimPrefix_erases _)
    | (maintenance_head xmitSplicePrefix; exact xmitSplicePrefix_erases _ _)
    | (maintenance_head loopbackSendPrefix; exact loopbackSendPrefix_erases _ _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem wgXmitPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (x : WgXmitContracts I) (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (wgXmitPrefix family addr pkts mtu) := by
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe
        (liftWGPrefix (StateT.lift a)) (fun _ h w _ => I h w) :=
    AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient a _))
  have routing {α : Type} (a : Net.M α) :
      StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe
        (liftWGPrefix (liftRouting a)) (fun _ h w _ => I h w) :=
    AmbientContracts.drop (c.store (fun _ => True) _ (fun initial =>
      hoare_liftRouting a _ (fun _ _ hi => hi)))
  change StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe _ (fun _ h w _ => I h w)
  unfold wgXmitPrefix rxBranch andPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head lookupDstPrefix; exact AmbientContracts.drop (lookupDstPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_ambient c t _)
    | (maintenance_head xmitTrimPrefix; exact xmitTrimPrefix_preserves c t _)
    | (maintenance_head xmitSplicePrefix; exact xmitSplicePrefix_preserves c _ _)
    | (maintenance_head loopbackSendPrefix; exact AmbientContracts.drop (loopbackSendPrefix_spec c (fun _ => True) _ _))
    | (maintenance_lift_action_head modifyDev; exact AmbientContracts.drop (x.errors (fun _ => True)))
    | (maintenance_lift_action_head liftRouting; exact routing _)
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.branch (fun _ => True) _ _))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.invariant (fun _ => True) _))
    | (maintenance_lift_action_head skipCutSites; exact ambient (AmbientM.skipCutSites _))
    | (maintenance_lift_action_head envOk; exact ambient (AmbientM.envOk _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => I h w) _ (fun _ h w _ hi => c.safe h w hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem wgXmitPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (x : ProductWgXmitContracts I) (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (wgXmitPrefix family addr pkts mtu)) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixEnsures I LifetimeEvent.Safe
        (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => I) := by
    rw [liftWGObserver_lift, liftWG_ambient]
    exact ProductAmbientContracts.drop (c.ambient (fun _ => True) a)
  have routing {α : Type} (a : Net.M α) :
      PrefixEnsures I LifetimeEvent.Safe
        (liftWGObserver (liftWGPrefix (liftRouting a))) (fun _ => I) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial =>
      hoare_liftRouting a _ (fun _ _ hi => hi)))
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold wgXmitPrefix rxBranch andPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ForIn.forIn; rw [liftWGObserver_forIn])
    | maintenance_product_lift
    | (maintenance_head lookupDstPrefix; exact ProductAmbientContracts.drop (lookupDstPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head sendStagedPacketsPrefix; exact sendStagedPacketsPrefix_preserves_product c t _)
    | (maintenance_head xmitTrimPrefix; exact xmitTrimPrefix_preserves_product c t _)
    | (maintenance_head xmitSplicePrefix; exact xmitSplicePrefix_preserves_product c _ _)
    | (maintenance_head loopbackSendPrefix; exact ProductAmbientContracts.drop (loopbackSendPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_lift_action_head modifyDev; exact ProductAmbientContracts.drop (x.errors (fun _ => True)))
    | (maintenance_lift_action_head liftRouting; exact routing _)
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head skipCutSites; exact ambient (AmbientM.skipCutSites _))
    | (maintenance_lift_action_head envOk; exact ambient (AmbientM.envOk _))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixEnsures.forInInvariant _ _ _ (fun _ => I) _ (fun _ => c.safe))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

end Leanux.Proofs.WG.Lifetimes
