import Leanux.Proofs.WG.Lifetimes.DeviceXmit
import Leanux.Proofs.Logged.PrefixControl
import Leanux.Proofs.Framing.Stack
import Leanux.Env.Batch

/-! Actual receive-side stack callbacks. IPv4 TCP replies re-enter the observed
transmit entry. IPv6 and the other input predicates are access-free with respect
to peer, keypair and packet stores. Source coverage is separate from framing. -/
set_option maxHeartbeats 800000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def reply4Prefix (dst : Nat) (bytes : List UInt8) : MixedM Unit := do
  liftPrefix (skipCut ([.inetEhashSecret] ++ allocCuts))
  let w ← liftPrefix (get : M World)
  let d ← liftPrefix getDev
  let mtu := ((w.routes.find? fun (f,a,_) => f == 4 && a == dst).map (·.2.2)).getD d.mtu
  discard <| wgXmitPrefix 4 dst [{bytes, csum := none, mtu}] mtu

theorem reply4Prefix_erases (dst : Nat) (bytes : List UInt8) :
    ErasesPrefix (reply4Prefix dst bytes) (Stack.reply4 dst bytes) := by
  unfold reply4Prefix Stack.reply4
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | exact wgXmitPrefix_erases _ _ _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | intro_forall

theorem reply4Prefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (x : WgXmitContracts I) (dst : Nat) (bytes : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (reply4Prefix dst bytes) := by
  unfold reply4Prefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | exact wgXmitPrefix_preserves c t x _ _ _ _
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (skipCut_sameKernel _))
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w a v hr; cases hr; rfl))
    | exact PrefixPreserves.pure c.safe _
    | apply PrefixPreserves.bind
    | intro_forall

def receive4Prefix (pkt : List UInt8) : MixedM Unit := do
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let ihl := byte 0 % 16
  -- row 1 (ip_rcv_core, ip_input.c:496): ihl < 5; row 2: tot_len < ihl*4
  -- at the pull (:506); row 14: options (ip_rcv_options)
  if ihl < 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 1 (ihl < 5: ip_rcv_core drops it)")
  if ihl > 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 14 (IPv4 options)")
  let totLen := WG.beAt pkt 2 2
  if totLen != pkt.length then liftPrefix (invariant "consume_data_done trims to tot_len")
  -- row 3: ip_fast_csum over the header
  if onesSum (pkt.take 20) != 0xffff then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 3 (a bad IPv4 header checksum)")
  let src := WG.beAt pkt 12 4
  let dst := WG.beAt pkt 16 4
  let top := src / 2 ^ 24
  -- rows 5-11: the route (ip_route_input_slow): martian sources, zeronet
  -- and loopback destinations, the limited broadcast, multicast groups
  if src ≥ 0xe0000000 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 5 (a multicast or limited-broadcast source)")
  if dst == 0xffffffff then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 10 (the limited broadcast destination)")
  if top == 0 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 6 (a zeronet source)")
  if dst / 2 ^ 24 == 0 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 7 (a zeronet destination)")
  if dst / 2 ^ 24 == 127 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 8 (a loopback destination, route_localnet 0)")
  if top == 127 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 9 (a loopback source)")
  if dst / 2 ^ 28 == 0xe then liftPrefix (Leanux.Env.Stack.excluded "2.2 rows 11a-11c (a multicast destination)")
  -- row 12: wg0's own address as the source (fib_validate_source)
  if src == WG0_ADDR4 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 12 (wg0's own address as the source)")
  -- row 13: a destination that is not local (forwarding off: ip_error, no ICMP)
  if dst != WG0_ADDR4 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 13 (a destination other than wg0's address)")
  -- row 15: fragments
  if WG.beAt pkt 6 2 % 0x4000 != 0 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 15 (a fragment)")
  let protocol := byte 9
  if protocol == 6 then
    -- row 17: tcp_v4_rcv (tcp_ipv4.c:2209-2231): a pullable header with
    -- doff >= 5, else silent; TCP options are a shape the mirror refuses
    if totLen < 40 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 17 (a TCP segment shorter than its header)")
    let doff := byte 32 / 16
    if doff < 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 17 (doff < 5)")
    if doff > 5 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 17 (TCP options)")
    -- no socket: tcp_v4_send_reset; a segment with RST is never answered
    if byte 33 / 4 % 2 == 1 then liftPrefix (Leanux.Env.Stack.excluded "2.4.1 (a segment with RST is not answered)")
    reply4Prefix src (Stack.rst4 pkt)
    return
  if protocol != 17 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 16 (a protocol without a handler: ICMP protocol unreachable)")
  -- rows 18-21: the UDP length against the IP payload
  let ulen := WG.beAt pkt 24 2
  if ulen > totLen - 20 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 18 (ulen beyond the IPv4 payload)")
  if ulen < 8 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 19 (ulen < 8)")
  if ulen < totLen - 20 then liftPrefix (Leanux.Env.Stack.excluded "2.2 row 20 (a datagram trimmed to ulen)")
  -- rows 22-24: the port map of the fixture
  let dport := WG.beAt pkt 22 2
  if dport != SENDER_PORT then
    if (← liftPrefix getK).wg.any (fun d => d.running && dport == d.incomingPort) then
      liftPrefix (Leanux.Env.Stack.excluded "2.2 row 24 (wg0's own listen port: a nested receive)")
    liftPrefix (Leanux.Env.Stack.excluded "2.2 row 22 (no socket at the port: ICMP port unreachable)")
  -- row 23: delivered to the sender, with the inner TOS (after the ECN
  -- rewrite) and the destination its `IPV6_PKTINFO` reports (v4-mapped)
  liftPrefix (modify fun w => { w with senderInbox := w.senderInbox ++
    [{ family := AF_INET, addr := src, port := WG.beAt pkt 20 2, bytes := pkt.drop 28, tos := byte 1,
       dst := 0xffff00000000 + dst }] })

theorem receive4Prefix_erases (pkt : List UInt8) :
    ErasesPrefix (receive4Prefix pkt) (Stack.receive4 pkt) := by
  unfold receive4Prefix Stack.receive4
  repeat' first
    | with_reducible exact reply4Prefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible exact erasesPrefix_lift_failure_bind (Stack.excluded _) (stackExcluded_failure _) _ _
    | with_reducible exact erasesPrefix_lift_failure_bind (invariant _) (fun _ => ⟨_, rfl⟩) _ _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | intro_forall
    | dsimp only
    | split

theorem receive4Prefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (x : WgXmitContracts I) (pkt : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (receive4Prefix pkt) := by
  unfold receive4Prefix
  repeat' first
    | with_reducible exact reply4Prefix_preserves c t x _ _
    | with_reducible exact PrefixPreserves.lift_failure_bind c.safe (Stack.excluded _) (stackExcluded_failure _) _
    | with_reducible exact PrefixPreserves.lift_failure_bind c.safe (invariant _) (fun _ => ⟨_, rfl⟩) _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w a v hr; cases hr; rfl))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (stackExcluded_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.bind
    | intro_forall
    | dsimp only
    | split
  all_goals exact AmbientContracts.drop (c.kernel (fun _ => True) _
    (by intro w a v hr; cases hr; rfl))

def stackReceivePrefix (pkt : List UInt8) : MixedM Unit := do
  let version := (pkt.headD 0).toNat / 16
  if version == 4 then receive4Prefix pkt
  else if version == 6 then liftPrefix (Stack.receive6 pkt)
  else liftPrefix (invariant "consume_data_done passed a packet that is neither IPv4 nor IPv6")

theorem stackReceivePrefix_erases (pkt : List UInt8) :
    ErasesPrefix (stackReceivePrefix pkt) (Stack.receive pkt) := by
  unfold stackReceivePrefix Stack.receive
  dsimp only
  split
  · exact receive4Prefix_erases _
  · split <;> exact erasesPrefix_lift _

theorem stackReceivePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (x : WgXmitContracts I) (pkt : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (stackReceivePrefix pkt) := by
  unfold stackReceivePrefix
  dsimp only
  split
  · exact receive4Prefix_preserves c t x _
  · split
    · exact AmbientContracts.drop (c.kernel (fun _ => True) _ (stackReceive6_sameKernel _))
    · exact AmbientContracts.drop (c.invariant (fun _ => True) _)

def stackFlushPrefix (pkts : List (List UInt8)) : MixedM Unit := pkts.forM stackReceivePrefix

theorem stackFlushPrefix_erases (pkts : List (List UInt8)) :
    ErasesPrefix (stackFlushPrefix pkts) (pkts.forM Leanux.Env.deliverInner) := by
  exact erasesPrefix_forM pkts stackReceivePrefix Leanux.Env.deliverInner stackReceivePrefix_erases

theorem stackFlushPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (x : WgXmitContracts I) (pkts : List (List UInt8)) :
    PrefixPreserves I LifetimeEvent.Safe (stackFlushPrefix pkts) :=
  PrefixPreserves.forM pkts stackReceivePrefix c.safe (stackReceivePrefix_preserves c t x)

def rxPollStackPrefix (pid : PeerId) (budget : Nat) : MixedM Nat :=
  rxPollPrefix pid budget stackFlushPrefix

theorem rxPollStackPrefix_erases (pid : PeerId) (budget : Nat) :
    ErasesPrefix (rxPollStackPrefix pid budget)
      (rxPoll pid budget (fun pkts => pkts.forM Leanux.Env.deliverInner)) :=
  rxPollPrefix_erases pid budget _ _ stackFlushPrefix_erases

theorem rxPollStackPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (r : RxContracts I) (x : WgXmitContracts I) (pid : PeerId) (budget : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (rxPollStackPrefix pid budget) :=
  rxPollPrefix_preserves_ambient c t r pid budget _ (stackFlushPrefix_preserves c t x)

end Leanux.Proofs.WG.Lifetimes
