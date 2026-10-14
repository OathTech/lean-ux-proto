import Leanux.Proofs.WG.Lifetimes.ReceivePoll
import Leanux.Proofs.WG.Lifetimes.LoopbackAccess

/-! The complete original transmit entry, including its error/loopback arms,
queue trimming and both getters in the staged-packet splice. The scalar error
counter has an explicit separate contract; packet values acquire store identities
only in the already observed staging caller. -/
set_option maxHeartbeats 800000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

structure WgXmitContracts (I : List LifetimeEvent → World → Prop) : Prop where
  errors : ∀ P, AmbientSpec I P
    (liftPrefix (modifyDev fun d => {d with txErrors := d.txErrors + 1})) (fun _ => P)

theorem allocationWgXmit : WgXmitContracts AllocationInv where
  errors := by
    intro P
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.safe)
    intro h w x v hi hr
    have hf : (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
      cases hr
      unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
      simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
      rfl
    have he : identityView v = identityView w := congrArg Prod.fst hf
    exact ⟨hi.1.congr he (congrArg Prod.snd hf), he ▸ hi.2⟩

def xmitTrim (pid : PeerId) : M Unit := do
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
      liftPrefix (modifyDev fun d => { d with txDropped := d.txDropped + 1 })
    else break

def xmitSplice (pid : PeerId) (packets : List Packet) : M Unit := do
  setPeer pid { (← getPeer pid) with staged := (← getPeer pid).staged ++ packets }

def xmitSplicePrefix (pid : PeerId) (packets : List Packet) : MixedM Unit := do
  setPeerMixed pid { (← getPeerMixed pid) with staged := (← getPeerMixed pid).staged ++ packets }

theorem xmitSplicePrefix_erases (pid : PeerId) (packets : List Packet) :
    ErasesPrefix (xmitSplicePrefix pid packets) (xmitSplice pid packets) :=
  erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
    erasesPrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _))

theorem xmitSplicePrefix_preserves (c : AmbientContracts I) (pid : PeerId) (packets : List Packet) :
    PrefixPreserves I LifetimeEvent.Safe (xmitSplicePrefix pid packets) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  apply PrefixEnsures.bind (c.getPeer_frame (fun s => True ∧ s.1.slots pid = some p.internalId) pid)
  intro q
  exact c.setPeer (fun _ => True) pid {p with staged := q.staged ++ packets}

theorem xmitTrimPrefix_erases (pid : PeerId) :
    ErasesPrefix (xmitTrimPrefix pid) (xmitTrim pid) := by
  unfold xmitTrimPrefix xmitTrim
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | split
    | (intro_forall; try dsimp only)

theorem xmitTrimPrefix_preserves (c : AmbientContracts I) (t : TxContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (xmitTrimPrefix pid) := by
  unfold xmitTrimPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) pid))
  intro initial
  apply PrefixPreserves.bind
  · apply PrefixPreserves.range _ _ _ c.safe
    intro idx acc
    apply AmbientContracts.drop (Q := fun _ _ => True)
    apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
    intro p
    apply PrefixEnsures.bind (c.branch (fun s => True ∧ s.1.slots pid = some p.internalId) _ _)
    intro trim
    split
    · apply PrefixEnsures.bind (c.setPeer (fun _ => True) pid {p with staged := p.staged.drop 1})
      intro _
      exact PrefixEnsures.bind (t.device (fun _ => True) (.dropped 1))
        (fun _ => c.pure (fun _ => True) _)
    · exact (c.pure (fun s => True ∧ s.1.slots pid = some p.internalId) _).consequence
        (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, True.intro⟩)
  · intro _
    exact PrefixPreserves.pure c.safe _

def wgXmitSource (family addr : Nat) (pkts : List Packet) (mtu : Nat) : M Int := do
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
  let err (ret : Int) : M Int := do
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
  let some first := pkts.head? | liftPrefix (invariant "wg_xmit without a packet")
  let realProtocol := match first.bytes with
    | b :: _ => if b.toNat / 16 == 4 then ETH_P_IP else if b.toNat / 16 == 6 then ETH_P_IPV6 else 0
    | [] => 0
  let skbProtocol := if family == 4 then ETH_P_IP else ETH_P_IPV6
  -- `real_protocol && skb->protocol == real_protocol`
  let ok ← andPrefix (rxBranch .checkProtoParsed (realProtocol != 0))
    (rxBranch .checkProtoMatches (skbProtocol == realProtocol))
  if ← rxBranch .xmitBadProtocol !ok then
    liftPrefix (modifyDev fun d => {d with txErrors := d.txErrors + 1})
    return -EPROTONOSUPPORT
  for p in pkts do
    let field (off len : Nat) := ((p.bytes.drop off).take len).foldl (fun acc b => acc * 256 + b.toNat) 0
    let dst := if family == 4 then field 16 4 else field 24 16
    if dst != addr then liftPrefix (invariant "the environment's destination disagrees with the packet header")
  let err (ret : Int) : MixedM Int := do
    -- err_icmp: icmp_ndo_send / icmpv6_ndo_send (cut points, whose rate limit
    -- and IP output draw cut-site choices), then err. The error is sent iff
    -- the rate limits allowed it, and then `icmp_global_consume` drew
    -- (icmp.c:310-339, ipv6/icmp.c:195-238: type 3 / type 1 is in the
    -- default ratemask, wg0 is not loopback, the reply's route is local);
    -- the ICMP's loopback delivery raises NET_RX, whose section runs at
    -- `__dev_queue_xmit`'s `rcu_read_unlock_bh` (`loopbackSend`).
    if !(← rxBranch .xmitErrorInet (family == 4)) then _ ← rxBranch .xmitErrorInet6 (family == 6)
    let drawn ← liftPrefix (skipCutSites ([.icmpCredit, .ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts))
    loopbackSendPrefix [] (drawn.contains (HiddenSite.icmpCredit).info.id)
    liftPrefix (modifyDev fun d => { d with txErrors := d.txErrors + 1 })   -- DEV_STATS_INC(dev, tx_errors)
    return ret
  let peer ← lookupDstPrefix family addr
  if ← rxBranch .xmitNoPeer peer.isNone then
    if !(← rxBranch .xmitNoPeerInet (family == 4)) then _ ← rxBranch .xmitNoPeerInet6 (family == 6)
    return ← err (-ENOKEY)
  let some pid := peer | liftPrefix (invariant "unreachable")
  let epFamily := (← getPeerMixed pid).endpoint.map (·.family) |>.getD 0
  if ← andPrefix (rxBranch .xmitEndpointNotInet (epFamily != AF_INET)) (rxBranch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
    peerPutMixed peer   -- err_peer
    return ← err (-EDESTADDRREQ)
  _ ← rxBranch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
  -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
  if !(← rxBranch .xmitNotGso (pkts.length < 2)) then
    -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
    -- an allocation inside skb_segment fails (A's domain, `envOk`)
    if ← rxBranch .xmitGsoError !(← liftPrefix (envOk .skbSegment)) then
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
    ErasesPrefix (wgXmitPrefix family addr pkts mtu) (wgXmit family addr pkts mtu) := by
  rw [wgXmitSource_eq]
  unfold wgXmitPrefix wgXmitSource
  repeat' first
    | contradiction
    | with_reducible exact lookupDstPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact xmitTrimPrefix_erases _
    | with_reducible exact xmitSplicePrefix_erases _ _
    | with_reducible exact loopbackSendPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | (intro_forall <;> try simp_all only [Option.some.injEq, reduceCtorEq])
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, reduceCtorEq])

theorem wgXmitPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (x : WgXmitContracts I) (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (wgXmitPrefix family addr pkts mtu) := by
  unfold wgXmitPrefix
  repeat' first
    | contradiction
    | with_reducible exact AmbientContracts.drop (lookupDstPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact c.peerPut _
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c t _
    | with_reducible exact xmitTrimPrefix_preserves c t _
    | with_reducible exact xmitSplicePrefix_preserves c _ _
    | with_reducible exact AmbientContracts.drop (loopbackSendPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (x.errors (fun _ => True))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (skipCutSites_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (envOk_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.unsupported (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall <;> try simp_all only [Option.some.injEq, reduceCtorEq])
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, reduceCtorEq])

end Leanux.Proofs.WG.Lifetimes
