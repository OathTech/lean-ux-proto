import Leanux.WG.Device
import Leanux.WG.RxData
import Leanux.Env.IpStack
import Leanux.Net.Route

/-!
# The IP stack on the receive side: what Linux does with an inner packet

W5+W6 (docs/2026-10-06-w5-w6-receive.md, sections 2, 4.1 and 4.2; revision
v3, the WireGuard boundary [USER 2026-10-07]). The stack between
`napi_gro_receive` and the fixture's sockets is a cut: the environment
walks the input predicate of sections 2.2 and 2.3 in Linux's order and ends
in one of three outcomes:
- **deliver**: a plain UDP datagram to wg0's address at the sender's port,
  from an allowed, non-martian source, with a correct header checksum and
  `ulen` equal to the payload: appended to the sender's inbox with its TOS
  (the inner header's, after the ECN rewrite) — 2.2 row 23 and the IPv6
  counterpart;
- **react**: an IPv4 TCP segment to wg0's address finds no socket, and
  Linux answers it with a RST (2.4.1) that re-enters `wg_xmit` from the NAPI
  poll's NET_RX section with `CHECKSUM_NONE` — 2.2 row 17;
- **`unsupported`** for every other row: the stack's silent drops and trims,
  the multicast and broadcast destinations, the IPv6 TCP segment, the
  ICMP-answered packets, fragments, options and extension headers — each
  "excluded: beyond the WireGuard boundary", with the row as the reason, so a
  trace that hits one fails with the Linux arm in the message. There is no
  silent pass and no comparison-side mask: a packet forced through Linux
  fails on the unexplained bytes in the inbox or the unexplained records.
-/

namespace Leanux.Env.Stack
open Leanux Leanux.WG Leanux.Env

/-- An excluded row (v3, section 14): fail-noisy, naming the Linux row. -/
def excluded (row : String) : M Unit :=
  unsupported s!"excluded: beyond the WireGuard boundary: {row}"

/-- `csum16_add(csum, addend)` (include/net/checksum.h) on the IPv4 header's
    check field as the kernel holds it on x86: the `__sum16` is added in
    memory order (little-endian), with the carry folded back in 16 bits
    (`res = csum + addend; res + (res < csum)`). `check` is the field's
    big-endian value; `addLe` the addend as the kernel's u16 (`htons(x)` read
    on a little-endian CPU); the result is the field's big-endian value. -/
def csum16Add (check addLe : Nat) : Nat :=
  let le := check % 256 * 256 + check / 256
  let res := (le + addLe) % 65536
  let res := if res < le then (res + 1) % 65536 else res
  res % 256 * 256 + res / 256

/-- The IPv4 TCP RST Linux sends for a segment to wg0 with no socket
    (`tcp_v4_rcv` → `no_tcp_socket` → `tcp_v4_send_reset(NULL, …)`,
    tcp_ipv4.c:737-920; `ip_send_unicast_reply`, ip_output.c:1603-1677;
    design 2.4.1, verified: DF, id 0), from the inner packet `pkt` (ihl 5,
    no TCP options): dest and source swapped, `doff` 5, RST; with ACK:
    `seq = ack_seq`; without: ACK and `ack_seq = seq + syn + fin + payload`;
    window 0, no urgent pointer, the TCP checksum folded in software
    (`CHECKSUM_NONE`); the IP header: TOS = the inner TOS with the ECN bits
    cleared (`inet_sk(sk)->tos = tos & ~INET_ECN_MASK`), `tot_len` 40, id 0,
    DF (the control socket's `IP_PMTUDISC_DO`), TTL 64, protocol 6, from the
    inner destination to the inner source. -/
def rst4 (pkt : List UInt8) : List UInt8 :=
  let b (i : Nat) : Nat := (pkt.getD i 0).toNat
  let src := beBytes (beAt pkt 12 4) 4
  let dst := beBytes (beAt pkt 16 4) 4
  let sport := beAt pkt 20 2
  let dport := beAt pkt 22 2
  let seq := beAt pkt 24 4
  let ackSeq := beAt pkt 28 4
  let doff := b 32 / 16
  let flags := b 33
  let payloadLen := pkt.length - 20 - 4 * doff
  let (rseq, rack, rflags) :=
    if flags / 16 % 2 == 1 then (ackSeq, 0, 4)   -- th->ack: seq = ack_seq
    else (0, (seq + flags / 2 % 2 + flags % 2 + payloadLen) % 2 ^ 32, 4 + 16)
  let th (check : Nat) := beBytes dport 2 ++ beBytes sport 2 ++ beBytes rseq 4 ++ beBytes rack 4
    ++ [0x50, UInt8.ofNat rflags] ++ beBytes 0 2 ++ beBytes check 2 ++ beBytes 0 2
  -- csum_tcpudp_magic over the pseudo header, then the header: csum_fold
  let tcpCheck := 0xffff - onesSum (dst ++ src ++ [0, 6] ++ beBytes 20 2 ++ th 0)
  let tos := b 1 / 4 * 4
  let ip (check : Nat) := [0x45, UInt8.ofNat tos] ++ beBytes 40 2 ++ [0, 0, 0x40, 0, 64, 6] ++ beBytes check 2
    ++ dst ++ src
  ip (0xffff - onesSum (ip 0)) ++ th tcpCheck

/-- A reply the stack built re-enters `wg_xmit` from the NAPI poll's NET_RX
    section (`ip_local_out` → the default route via wg0 → `dev_queue_xmit`),
    as a `CHECKSUM_NONE` packet (`encryptPacket`'s checksum-help decision
    takes its false outcome). Before it, the first TCP segment of a boot may
    have drawn the established-hash secret (early demux or the lookup,
    `inet_ehashfn`): a cut. The encrypt work the transmit queues is picked up
    where D2 picks up the confirmation flush: `runCryptWorkers` after the
    decrypt worker, or inside its `cond_resched` (`Env.condResched`). -/
def reply4 (dst : Nat) (bytes : List UInt8) : M Unit := do
  -- the ehash secret, and the reply's own skb allocations (ip_append_data:
  -- `AllocSite.ipAppendDataSkb`, recorded when a chunk arms the ranges)
  skipCut ([.inetEhashSecret] ++ allocCuts)
  -- lane C: `ip_send_unicast_reply` (ip_output.c:1603-1677) routes the reply
  -- from the segment's destination (an interface address, `__ip_dev_find`'s
  -- found arm) to its source; a route error drops it (:1631-1632). W4:
  -- `wg_xmit` reads `dst_mtu` (device.c:173): the route's metric when the
  -- fixture's route carries one, else `dev->mtu`. `ip_finish_output2` on
  -- wg0: the device's one neighbour (`Net.neighbourClassify`).
  let saddr := WG.beAt bytes 12 4
  match ← Net.routeOutput4 saddr dst with
  | .error _ => return
  | .ok r =>
    if r.dev != WG0_IFINDEX then unsupported "a stack reply routed away from wg0"
    let devMtu := (← getDev).mtu
    let mtu := if r.mtu != 0 then r.mtu else devMtu
    Net.neighbourClassify WG0_IFINDEX
    discard <| WG.wgXmit 4 dst [{ bytes, csum := none, mtu }] mtu

/-- The IPv4 input predicate (2.2) for an inner packet of `pkt.length`
    bytes, which `wg_packet_consume_data_done` trimmed to `tot_len` and
    marked `CHECKSUM_UNNECESSARY`. -/
def receive4 (pkt : List UInt8) : M Unit := do
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let ihl := byte 0 % 16
  -- row 1 (ip_rcv_core, ip_input.c:496): ihl < 5; row 2: tot_len < ihl*4
  -- at the pull (:506); row 14: options (ip_rcv_options)
  if ihl < 5 then excluded "2.2 row 1 (ihl < 5: ip_rcv_core drops it)"
  if ihl > 5 then excluded "2.2 row 14 (IPv4 options)"
  let totLen := WG.beAt pkt 2 2
  if totLen != pkt.length then invariant "consume_data_done trims to tot_len"
  -- row 3: ip_fast_csum over the header
  if onesSum (pkt.take 20) != 0xffff then excluded "2.2 row 3 (a bad IPv4 header checksum)"
  let src := WG.beAt pkt 12 4
  let dst := WG.beAt pkt 16 4
  let top := src / 2 ^ 24
  -- rows 5-11: the route (ip_route_input_slow): martian sources, zeronet
  -- and loopback destinations, the limited broadcast, multicast groups
  if src ≥ 0xe0000000 then excluded "2.2 row 5 (a multicast or limited-broadcast source)"
  if dst == 0xffffffff then excluded "2.2 row 10 (the limited broadcast destination)"
  if top == 0 then excluded "2.2 row 6 (a zeronet source)"
  if dst / 2 ^ 24 == 0 then excluded "2.2 row 7 (a zeronet destination)"
  if dst / 2 ^ 24 == 127 then excluded "2.2 row 8 (a loopback destination, route_localnet 0)"
  if top == 127 then excluded "2.2 row 9 (a loopback source)"
  if dst / 2 ^ 28 == 0xe then excluded "2.2 rows 11a-11c (a multicast destination)"
  -- rows 12 and 13, lane C: `ip_route_input_slow`'s lookup on the trie
  -- (route.c:2347-2376) and `fib_validate_source`'s fast path
  -- (fib_frontend.c:421-451): a local destination from a local source is a
  -- martian source (row 12, silent); no route or a route the stack will
  -- not forward is `ip_error` with forwarding off (row 13: counted, no
  -- ICMP, silent, W5 2.4.7); a broadcast route is udp.c's broadcast
  -- delivery, outside this module
  match ← Net.routeInput4 src dst with
  | .local true => excluded "2.2 row 12 (a local source: fib_validate_source's -EINVAL)"
  | .local false => pure ()
  | .noRoute | .notLocal => return   -- row 13: ip_error, INADDRERRORS, no ICMP
  | .broadcast => unsupported "a decrypted packet to a broadcast route (udp.c's broadcast delivery)"
  -- row 15: fragments
  if WG.beAt pkt 6 2 % 0x4000 != 0 then excluded "2.2 row 15 (a fragment)"
  let protocol := byte 9
  if protocol == 6 then
    -- row 17: tcp_v4_rcv (tcp_ipv4.c:2209-2231): a pullable header with
    -- doff >= 5, else silent; TCP options are a shape the mirror refuses
    if totLen < 40 then excluded "2.2 row 17 (a TCP segment shorter than its header)"
    let doff := byte 32 / 16
    if doff < 5 then excluded "2.2 row 17 (doff < 5)"
    if doff > 5 then excluded "2.2 row 17 (TCP options)"
    -- no socket: tcp_v4_send_reset; a segment with RST is never answered
    if byte 33 / 4 % 2 == 1 then excluded "2.4.1 (a segment with RST is not answered)"
    reply4 src (rst4 pkt)
    return
  if protocol != 17 then excluded "2.2 row 16 (a protocol without a handler: ICMP protocol unreachable)"
  -- rows 18-21: the UDP length against the IP payload
  let ulen := WG.beAt pkt 24 2
  if ulen > totLen - 20 then excluded "2.2 row 18 (ulen beyond the IPv4 payload)"
  if ulen < 8 then excluded "2.2 row 19 (ulen < 8)"
  if ulen < totLen - 20 then excluded "2.2 row 20 (a datagram trimmed to ulen)"
  -- rows 22-24: the port map of the fixture
  let dport := WG.beAt pkt 22 2
  if dport != SENDER_PORT then
    if (← getWG).dev.any (fun d => d.running && dport == d.incomingPort) then
      excluded "2.2 row 24 (wg0's own listen port: a nested receive)"
    excluded "2.2 row 22 (no socket at the port: ICMP port unreachable)"
  -- row 23: delivered to the sender, with the inner TOS (after the ECN
  -- rewrite) and the destination its `IPV6_PKTINFO` reports (v4-mapped)
  modifyEnv fun w => { w with senderInbox := w.senderInbox ++
    [{ family := AF_INET, addr := src, port := WG.beAt pkt 20 2, bytes := pkt.drop 28, tos := byte 1,
       dst := 0xffff00000000 + dst }] }

/-- The IPv6 input predicate (2.3). -/
def receive6 (pkt : List UInt8) : M Unit := do
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let payloadLen := WG.beAt pkt 4 2
  if payloadLen + 40 != pkt.length then invariant "consume_data_done trims to the payload length"
  let src := WG.beAt pkt 8 16
  let dst := WG.beAt pkt 24 16
  -- rows 1-2 (ip6_rcv_core): loopback addresses, multicast scopes, a multicast source
  if src == 1 || dst == 1 then excluded "2.3 row 1 (::1 as the source or destination on wg0)"
  if dst / 2 ^ 112 == 0xff01 then excluded "2.3 row 1a (a scope-1 multicast destination)"
  if dst / 2 ^ 112 == 0xff00 then excluded "2.3 row 1b (a scope-0 multicast destination)"
  if src / 2 ^ 120 == 0xff then excluded "2.3 row 2 (a multicast source)"
  let nextHeader := byte 6
  -- row 3: an empty payload (then by next header); row 4, 6: extension headers
  if payloadLen == 0 then excluded "2.3 row 3 (payload_len 0)"
  if nextHeader == 0 then excluded "2.3 row 4 (a hop-by-hop header)"
  if nextHeader == 43 || nextHeader == 44 || nextHeader == 60 then excluded "2.3 row 6 (an extension header)"
  -- rows 4a-4b: multicast destinations; row 5: not local
  if dst / 2 ^ 120 == 0xff then excluded "2.3 rows 4a-4b (a multicast destination)"
  if dst != WG0_ADDR6 then excluded "2.3 row 5 (a destination other than wg0's address: forwarding off)"
  -- row 18: unverified sources; link-local inner sources are listed extras
  if src == 0 || src / 2 ^ 32 == 0xffff then excluded "2.3 row 18 (an unspecified or v4-mapped source)"
  if src / 2 ^ 118 == 0x3fa then excluded "2.3 row 17 (a link-local inner source: not probed)"
  if nextHeader == 6 then excluded "2.3 row 8 (an IPv6 TCP segment: the IPv6 RST)"
  if nextHeader != 17 then excluded "2.3 row 7 (an unknown next header: ICMPv6 parameter problem)"
  -- rows 9-12: the UDP length; rows 13-14: a zero checksum; row 16: no socket
  let ulen := WG.beAt pkt 44 2
  if ulen > payloadLen then excluded "2.3 row 9 (ulen beyond the IPv6 payload)"
  if ulen == 0 then excluded "2.3 row 10 (ulen 0: the jumbo rule)"
  if ulen < 8 then excluded "2.3 row 11 (ulen < 8)"
  if ulen < payloadLen then excluded "2.3 row 12 (a datagram trimmed to ulen)"
  if WG.beAt pkt 46 2 == 0 then excluded "2.3 rows 13-14 (a zero UDP checksum)"
  let dport := WG.beAt pkt 42 2
  if dport != SENDER_PORT then
    if (← getWG).dev.any (fun d => d.running && dport == d.incomingPort) then
      excluded "2.3 (wg0's own listen port: a nested receive)"
    excluded "2.3 row 16 (no socket at the port: ICMPv6 port unreachable)"
  -- delivered to the sender, with the inner traffic class (after the ECN rewrite)
  modifyEnv fun w => { w with senderInbox := w.senderInbox ++
    [{ family := AF_INET6, addr := src, port := WG.beAt pkt 40 2, bytes := pkt.drop 48,
       tos := WG.beAt pkt 0 2 / 16 % 256, dst := dst }] }

/-- The delivery of an inner packet that GRO flushed at `napi_complete_done`
    (`gro_normal_list`, then the IPv4/IPv6 and UDP receive paths). -/
def receive (pkt : List UInt8) : M Unit := do
  let version := (pkt.headD 0).toNat / 16
  if version == 4 then receive4 pkt
  else if version == 6 then receive6 pkt
  else invariant "consume_data_done passed a packet that is neither IPv4 nor IPv6"

end Leanux.Env.Stack
