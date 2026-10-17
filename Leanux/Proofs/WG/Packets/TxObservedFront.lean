import Leanux.Proofs.WG.Packets.TxFront
import Leanux.Proofs.WG.Queues.RemovalAppends

/-! A literal factor of the existing lifetime observer at the completed staged
splice. Every access and failure record stays in the original order; the
following send and payment remain the original suffix. No capture is added. -/
namespace Leanux.Proofs.WG.Packets
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes CounterWindow

def txFrontPrefix (family addr : Nat) (pkts : List Packet) (mtu : Nat) : MixedM (Except Int PeerId) := do
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
    return .error (-EPROTONOSUPPORT)
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
    return .error (← err (-ENOKEY))
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  let epFamily := (← getPeerMixed pid).endpoint.map (·.family) |>.getD 0
  if ← andPrefix (rxBranch .xmitEndpointNotInet (epFamily != AF_INET)) (rxBranch .xmitEndpointNotInet6 (epFamily != AF_INET6)) then
    peerPutMixed peer   -- err_peer
    return .error (← err (-EDESTADDRREQ))
  _ ← rxBranch .xmitValidDst true   -- mtu = dst_mtu(skb_dst(skb))
  -- `if (!skb_is_gso(skb))` (device.c:176): a GSO skb arrives as its segments
  if !(← rxBranch .xmitNotGso (pkts.length < 2)) then
    -- skb_gso_segment(skb, 0) (device.c:179-186): `IS_ERR(segs)` only when
    -- an allocation inside skb_segment fails (A's domain, `envOk`)
    if ← rxBranch .xmitGsoError !(← liftWGPrefix (envOk .skbSegment)) then
      peerPutMixed peer   -- err_peer
      return .error (← err (-ENOMEM))
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
  return .ok pid

/-- The exact lifetime observer for the unchanged native suffix. -/
def txTailPrefix (pid : PeerId) : MixedM Int := do
  sendStagedPacketsPrefix pid
  peerPutMixed (some pid)
  return 0

/-- Factoring does not change the journal, including either stopped prefix. -/
theorem wgXmitPrefix_front_factor (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    wgXmitPrefix family addr pkts mtu = (do
      match ← txFrontPrefix family addr pkts mtu with
      | .error err => pure err
      | .ok pid => txTailPrefix pid) := by
  cases first : pkts.head? with
  | none => simp only [wgXmitPrefix,txFrontPrefix,first]; rfl
  | some packet =>
    simp only [wgXmitPrefix,txFrontPrefix,txTailPrefix,first]
    simp (config := {zeta := false}) only [bind_assoc,
      (pinned_const _private.Leanux.Proofs.WG.Packets.RoutingCuts.«0».Leanux.Proofs.WG.Packets.bind_if),pure_bind,bind_pure]
    all_goals repeat' first
      | rfl
      | apply (pinned_const _private.Leanux.Proofs.WG.Packets.RoutingCuts.«0».Leanux.Proofs.WG.Packets.bind_congr)
      | apply ite_congr rfl
      | (conv => rhs; rw [bind_assoc])
      | (conv => rhs; rw [(pinned_const _private.Leanux.Proofs.WG.Packets.RoutingCuts.«0».Leanux.Proofs.WG.Packets.bind_if)])
      | (conv => rhs; rw [pure_bind])
      | (conv => rhs; rw [bind_pure])
      | maintenance_intro
      | maintenance_reduce_match
      | (maintenance_match <;> dsimp only)


/-- The suffix erases to its actual WG/Ambient action on every input history. -/
theorem txTailPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (txTailPrefix pid) (txTail pid) := by
  unfold txTailPrefix txTail
  exact erasesStatePrefix_bind (sendStagedPacketsPrefix_erases pid) (fun _ =>
    erasesStatePrefix_bind (peerPutMixed_erases (some pid)) (fun _ => erasesStatePrefix_pure _))

private theorem txFront_erases_if {α : Type} (p : Prop) [Decidable p]
    (a b : MixedM α) (x y : WG.M α)
    (ha : ErasesStatePrefix a x) (hb : ErasesStatePrefix b y) :
    ErasesStatePrefix (if p then a else b) (if p then x else y) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using ha
  · simpa only [ite_eq_right hp] using hb

/-- The completed observed front erases to the exact native source cut,
including normal errno outcomes and every failed access prefix. -/
theorem txFrontPrefix_erases (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ErasesStatePrefix (txFrontPrefix family addr pkts mtu) (txFront family addr pkts mtu) := by
  cases first : pkts.head? with
  | none =>
    simp only [txFrontPrefix,txFront,txCheck,first]
    exact erasesStatePrefix_lift _
  | some packet =>
    simp only [txFrontPrefix,txFront,txCheck,txSelect,txError,txHeaders,txWalk,destinationField,first,
      Option.getD_some]
    simp (config := {zeta := false}) only [bind_assoc,
      (pinned_const _private.Leanux.Proofs.WG.Packets.RoutingCuts.«0».Leanux.Proofs.WG.Packets.bind_if),pure_bind]
    unfold rxBranch andPrefix WG.andM
    repeat' first
      | maintenance_erases_join
      | maintenance_erases_join_use
      | (maintenance_head lookupDstPrefix; exact lookupDstPrefix_erases _ _)
      | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
      | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
      | (maintenance_head xmitTrimPrefix; exact xmitTrimPrefix_erases _)
      | (maintenance_head xmitSplicePrefix; exact xmitSplicePrefix_erases _ _)
      | (maintenance_head loopbackSendPrefix; exact loopbackSendPrefix_erases _ _)
      | (maintenance_lift_head; exact erasesStatePrefix_lift _)
      | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
      | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
      | maintenance_erases_bind
      | maintenance_intro
      | maintenance_reduce
      | (maintenance_head ite; apply txFront_erases_if)
      | maintenance_reduce_match
      | (maintenance_match <;>
          simp (config := {zeta := false}) only [bind_assoc,
            (pinned_const _private.Leanux.Proofs.WG.Packets.RoutingCuts.«0».Leanux.Proofs.WG.Packets.bind_if),
            pure_bind])
      | maintenance_impossible_match


/-- The exact observed front only appends records, also on Stop. -/
theorem txFrontPrefix_appends (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    StateAppends (txFrontPrefix family addr pkts mtu) := by
  unfold txFrontPrefix rxBranch andPrefix lookupDstPrefix lookupPrefix peerGetMaybeZeroPrefix
    xmitTrimPrefix xmitSplicePrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (joint_append_head rxBranch; exact StateAppends.lift _)
    | (joint_append_head loopbackSendPrefix
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.RemovalAppends.«0».Leanux.Proofs.WG.Queues.RoutingJoint.loopback_appends) _ _)
    | joint_append_step

/-- Sending and paying the selected peer retain the existing journal prefix. -/
theorem txTailPrefix_appends (pid : PeerId) : StateAppends (txTailPrefix pid) := by
  unfold txTailPrefix
  exact (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationTail.«0».Leanux.Proofs.WG.Queues.RoutingJoint.staged_appends) pid |>.bind
    (fun _ => (StateAppends.focus _ _ _).bind (fun _ => StateAppends.pure _))

end Leanux.Proofs.WG.Packets
