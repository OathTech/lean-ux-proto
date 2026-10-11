import Leanux.WG.Device
import Leanux.WG.Data

/-!
# The IP stack on the transmit side: the packets the fixture's sender hands `wg_xmit`

Split out of `Leanux/Env.lean` at the interface commit (docs/2026-10-11-interface.md).
Owned by W4+W7's stream T (docs/2026-10-06-w4-w7-transmit-bulk.md, sections
12 and 15): `xmitPackets` with `XmitOpts` (IPv4 GSO, the route MTU,
fragmentation as `unsupported`), the `{224.0.0.1}` set, `setMtu`'s
consequences and the boundary `unsupported`s land here; `Env.lean` keeps
the hooks that call it (`xmitMulticastLoop`, the keepalive rule). Nothing
here runs a deferred unit: the file holds the stack's packet construction
and the checksum completion `encrypt_packet` asks of it.
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- The fixture's sender (`wg_inject`) is bound to this port on `[::]`
    (dual-stack); `wg_observe` drains what it received. -/
def SENDER_PORT : Nat := 51998

/-- The fixture's sender transmits (`wg_xmit`) to this UDP port. -/
def SEND_PORT : Nat := 40000

/-- wg0's addresses, added at `wg_up` (guest.c `route_into_wg0`): the
    source the sender's IP layer selects for a destination routed into wg0. -/
def WG0_ADDR4 : Nat := 0x0afffe01
def WG0_ADDR6 : Nat := 0xfd00ffff000000000000000000000001

/-- The largest UDP payload whose IP packet fits wg0's MTU (1420). -/
def MAX_XMIT_PAYLOAD4 : Nat := WG.DEVICE_MTU - 20 - 8
def MAX_XMIT_PAYLOAD6 : Nat := WG.DEVICE_MTU - 40 - 8

/-- `n` as `width` big-endian bytes. -/
def beBytes (n width : Nat) : List UInt8 :=
  (List.range width).reverse.map fun k => UInt8.ofNat (n / 256 ^ k % 256)

/-- The ones'-complement sum (end-around carry) of `bytes` as big-endian
    16-bit words (an odd tail padded with a zero byte), added to `init`, folded
    to 16 bits: what the kernel's `csum_partial` family computes. -/
def onesSum (bytes : List UInt8) (init : Nat := 0) : Nat := Id.run do
  let rec words : List UInt8 → Nat → Nat
    | a :: b :: rest, acc => words rest (acc + a.toNat * 256 + b.toNat)
    | [a], acc => acc + a.toNat * 256
    | [], acc => acc
  let mut s := words bytes init
  for _ in [0:8] do
    if s > 0xffff then s := s % 0x10000 + s / 0x10000
  return s

/-- Whether the sender's IP layer builds a packet to `addr` that the
    environment does not determine: an IPv6 link-local destination selects
    wg0's random link-local source address, and a multicast destination
    (224.0.0.0/4, ff00::/8) is sent with the socket's multicast hop limit and
    source. -/
def xmitBytesUnknown (family addr : Nat) : Bool :=
  (family == 4 && addr / 2 ^ 28 == 0xe) || (family == 6 && (addr / 2 ^ 118 == 0x3fa || addr / 2 ^ 120 == 0xff))

/-- The IP packet `wg_xmit` receives from the fixture's sender (`SEND_FD`,
    bound to `[::]:51998`, dual-stack; IPv4 goes as v4-mapped): the UDP
    datagram to `SEND_PORT` with `payload`, behind a UDP header and an IPv4 or
    IPv6 header, as docs/2026-10-04-d2-data-plane.md section 2 derives it
    from the fixture:
    - IPv4 (`__ip_make_skb`, `__ip_local_out`): version/ihl 0x45, tos 0,
      DF set and **id 0** (`IP_PMTUDISC_DO` on the sender: `ignore_df` is 0
      and the socket is unconnected, ip.h:559-589), TTL 64, protocol 17,
      the header checksum; source wg0's address.
    - IPv6 (`ip6_make_skb`, `__ip6_local_out`): traffic class 0, **flow
      label 0** (`IPV6_AUTOFLOWLABEL = 0` on the sender), payload length,
      next header 17, hop limit 64; source wg0's address.
    - UDP (`udp4_hwcsum`, `udp6_hwcsum_outgoing`): wg0 advertises
      `NETIF_F_HW_CSUM`, so the skb is `CHECKSUM_PARTIAL`: the check field
      holds the folded pseudo-header sum (`~csum_*_magic(..., 0)`), and
      `csum_start`/`csum_offset` name the UDP header and its check field.
    - `PACKET_CB(skb)->mtu` is `dst_mtu` of the route through wg0, 1420.
    A payload too large for the MTU fails `sendto` (or fragments, on IPv6),
    which is outside the domain. For the destinations of `xmitBytesUnknown`
    the bytes are not determined: the packet carries a zero source address
    as a placeholder, and `checksumHelp`, which every such packet meets
    before its bytes are read (encryption), is `unsupported`. -/
def xmitPacket (family addr : Nat) (payload : List UInt8) : M WG.Packet := do
  let ulen := 8 + payload.length
  if family == 4 then
    if payload.length > MAX_XMIT_PAYLOAD4 then unsupported "a transmitted payload beyond wg0's MTU"
    let src := if xmitBytesUnknown family addr then 0 else WG0_ADDR4
    let pseudo := onesSum (beBytes src 4 ++ beBytes addr 4 ++ [0, 17] ++ beBytes ulen 2)
    let udp := beBytes SENDER_PORT 2 ++ beBytes SEND_PORT 2 ++ beBytes ulen 2 ++ beBytes pseudo 2 ++ payload
    let hdr (check : Nat) := [0x45, 0] ++ beBytes (20 + ulen) 2 ++ [0, 0, 0x40, 0, 64, 17] ++ beBytes check 2
      ++ beBytes src 4 ++ beBytes addr 4
    -- ip_send_check: `ip_fast_csum` over the header with a zero check field
    let check := 0xffff - onesSum (hdr 0)
    return { bytes := hdr check ++ udp, csum := some (20, 6), mtu := WG.DEVICE_MTU }
  else if family == 6 then
    if payload.length > MAX_XMIT_PAYLOAD6 then unsupported "a transmitted payload beyond wg0's MTU"
    let src := if xmitBytesUnknown family addr then 0 else WG0_ADDR6
    let pseudo := onesSum (beBytes src 16 ++ beBytes addr 16 ++ beBytes ulen 4 ++ [0, 0, 0, 17])
    let udp := beBytes SENDER_PORT 2 ++ beBytes SEND_PORT 2 ++ beBytes ulen 2 ++ beBytes pseudo 2 ++ payload
    let hdr := [0x60, 0, 0, 0] ++ beBytes ulen 2 ++ [17, 64] ++ beBytes src 16 ++ beBytes addr 16
    return { bytes := hdr ++ udp, csum := some (40, 6), mtu := WG.DEVICE_MTU }
  else unsupported "a transmit family other than IPv4 or IPv6"

/-- `skb_checksum_help` (net/core/dev.c:3384-3431, a cut) of a
    `CHECKSUM_PARTIAL` packet: the ones'-complement sum from `csum_start` to
    the end (the check field holds the pseudo-header sum), folded and
    complemented into the check field, `csum_fold(csum) ?: CSUM_MANGLED_0`
    (a zero result is sent as 0xffff); the packet is then `CHECKSUM_NONE`.
    Only its failure is an environment outcome (`.skbChecksumHelp`). -/
def checksumHelp (pkt : WG.Packet) : M WG.Packet := do
  let some (start, offset) := pkt.csum | invariant "skb_checksum_help on a packet without CHECKSUM_PARTIAL"
  let version := (pkt.bytes.headD 0).toNat / 16
  let field (off len : Nat) := ((pkt.bytes.drop off).take len).foldl (fun acc b => acc * 256 + b.toNat) 0
  let dst := if version == 4 then field 16 4 else field 24 16
  if xmitBytesUnknown (if version == 4 then 4 else 6) dst then
    unsupported "a transmitted packet whose source or hop limit the fixture does not determine (link-local or multicast destination)"
  let folded := 0xffff - onesSum (pkt.bytes.drop start)
  let check := if folded == 0 then 0xffff else folded
  let at_ := start + offset
  if at_ + 2 > pkt.bytes.length then invariant "the checksum field lies beyond the packet"
  return { pkt with bytes := pkt.bytes.take at_ ++ beBytes check 2 ++ pkt.bytes.drop (at_ + 2), csum := none }

end Leanux.Env
