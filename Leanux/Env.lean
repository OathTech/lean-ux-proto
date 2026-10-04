import Leanux.WG.Device
import Leanux.WG.Receive
import Leanux.WG.Data
import Leanux.WG.RxData

/-!
# The environment model: the harness fixture and the WireGuard kworker

Not a mirror of C. This module holds what the trace's environment does, so
the mirror proper (`Leanux/WG`) contains only the C's data and control flow:
- the network fixture's listener port and the `wg_observe` operation, which
  waits, drains the fixture's listeners and reports wg0's counters;
- the fixture checks around `wg_up` (the device goes up once; its port must
  not be the fixture's);
- when the kworkers run: the handshake receive worker inside `wg_inject`,
  then the encrypt and tx workers it queued, and the (mirrored) handshake
  send worker at the end of the operation that queued it, which the guest
  waits for;
- where wg0's datagrams go over loopback.
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- The fixture's UDP listeners are on 127.0.0.1 and ::1 at this port. -/
def LISTEN_PORT : Nat := 51999

/-- The fixture's sender (`wg_inject`) is bound to this port on `[::]`
    (dual-stack); `wg_observe` drains what it received. -/
def SENDER_PORT : Nat := 51998

/-- Whether an endpoint is the fixture's sender. -/
def isSender (family addr port : Nat) : Bool :=
  port == SENDER_PORT && ((family == AF_INET && addr == 0x7f000001) || (family == AF_INET6 && addr == 1))

/-- What the sender's datagrams carry in their skb: loopback source and
    destination, the sender's port, the loopback interface (ifindex 1), and
    a zero DS field (the sender sets no TOS or traffic class). -/
def senderSource (family : Nat) : M SkbSource :=
  if family == 4 then pure { family := 4, saddr := 0x7f000001, sport := SENDER_PORT, daddr := 0x7f000001, iif := 1, tos := 0 }
  else if family == 6 then pure { family := 6, saddr := 1, sport := SENDER_PORT, daddr := 1, iif := 1, tos := 0 }
  else unsupported "an injection family other than IPv4 or IPv6"

/-- The guest waits `OBSERVE_WAIT_US` (0.4 s) after every injection, and
    fails any trace that runs longer than `REKEY_BOUND_NS` (4 s) after
    `wg_up`. So two consumed initiations are at least 0.4 s apart (and the
    first comes long after boot), and only a timer of more than 4 s cannot
    expire within the trace. -/
def INJECT_GAP_NS : Nat := 400000000
def TRACE_BOUND_SECONDS : Nat := 4

def timing : Timing where
  timerMayExpire s := s ≤ TRACE_BOUND_SECONDS

/-- The fixture's own `sendto` (into wg0's route, or to wg0's port): the IP
    output path draws the ident key and the ident, and may initialize the
    flow-hash secret; these are cut-site choices (choice-stream strategy,
    section 5). -/
def fixtureSend : M Unit :=
  skipCut [.ipIdentKey, .ipIdentReserve, .flowHashSecret]

/-- The IP packet `wg_xmit` receives from the fixture's sender: the UDP
    datagram behind a UDP header and an IPv4 or IPv6 header.
    INTERFACE STUB (D2 stream A computes the bytes, the partial checksum and
    the MTU, docs/2026-10-04-d2-data-plane.md section 2): until then only
    the length is right, which is all the pre-D2 paths read (a payload packet
    meeting a session is `unsupported`). -/
def xmitPacket (family _addr : Nat) (payload : List UInt8) : M WG.Packet :=
  return { bytes := List.replicate ((if family == 4 then 20 else 40) + 8 + payload.length) 0, mtu := WG.DEVICE_MTU }

/-- Whether an endpoint is one of the fixture's listeners. -/
def listenerFamily (e : Endpoint) : Option Nat :=
  if e.port != LISTEN_PORT then none
  else if e.family == AF_INET && e.addr == 0x7f000001 then some 4
  else if e.family == AF_INET6 && e.addr == 1 then some 6
  else none

/-- Deliver what wg0 sent (`World.sent`) over loopback: to the fixture's
    sender or a listener, which keep the bytes for `wg_observe`; another
    loopback port has no socket, so the datagram is dropped there (the send
    itself succeeded). Any other destination routes back into wg0, which is
    outside the domain. -/
def deliverSent : M Unit := do
  for dg in (← get).sent do
    let loopback := (dg.family == AF_INET && dg.addr / 2 ^ 24 == 127) || (dg.family == AF_INET6 && dg.addr == 1)
    if isSender dg.family dg.addr dg.port then
      -- from wg0's socket on the loopback address of the datagram's family
      -- (D2 stream A fixes how recvfrom reports it)
      let src := { family := dg.family, addr := if dg.family == AF_INET then 0x7f000001 else 1,
                   port := (← getDev).incomingPort, bytes := dg.bytes : InboxDatagram }
      modify fun w => { w with senderInbox := w.senderInbox ++ [src] }
    else match listenerFamily { family := dg.family, addr := dg.addr, port := dg.port } with
      | some 4 => modify fun w => { w with listenerV4 := w.listenerV4 ++ [dg.bytes] }
      | some _ => modify fun w => { w with listenerV6 := w.listenerV6 ++ [dg.bytes] }
      | none => if !loopback then unsupported "a datagram routed back into wg0"
  modify fun w => { w with sent := [] }

/-- A deferred unit's run. The kernel (the `net-choice` profile since the
    D1 sprint) opens a dispatch section per dispatch of a function in the
    armed set (`harness/linux.py`, `DISPATCH_SYMBOLS`); its start and
    stop records bracket it in the choice stream, so the order in which the
    kernel ran deferred units is checked rather than assumed.

    A worker that switched away at a `cond_resched` (`condResched`) resumes
    when the kernel's scheduler picks it again, which may be after workers
    the mirror cannot run first: its own callers, preempted further up the
    mirror's call stack. The mirror runs the rest of such a worker at once
    and leaves its stop pending; the stop's record is consumed where Linux
    recorded it (`skipAmbient`), and an operation ends with none pending
    (`Runner.executeTrace`). This assumes the resumed rests commute: they
    may read no hidden input (a read out of order is a mismatch) and touch
    no state the others read. On the modeled paths each rest is a worker's
    final empty ring or queue poll. -/
def runWorker (w : Worker) (body : M Unit) : M Unit := do
  _ ← hidden (.sectionStart w)
  -- whether this run switched away
  modify fun s => { s with yieldedWorkers := s.yieldedWorkers.filter (· != w.index) }
  body
  let stop := (HiddenSite.sectionStop w).info.id
  let deferred := (← get).yieldedWorkers.contains w.index && (← peekHiddenSite).isSome
    && (← peekHiddenSite) != some stop
  if deferred then modify fun s => { s with pendingStops := s.pendingStops ++ [stop] }
  else _ ← hidden (.sectionStop w)

/-- The worker whose section a record starts or stops, with `true` for a
    start; `none` for other records and for `net_rx_action`, a softirq,
    which the environment runs where its records say: nested where it is
    raised, or (D2) in ksoftirqd after a worker's switch. -/
def sectionOf (site : Nat) : Option (Worker × Bool) :=
  [Worker.sendWorker, .receiveWorker, .encryptWorker, .txWorker, .decryptWorker].findSome? fun w =>
    if site == (HiddenSite.sectionStart w).info.id then some (w, true)
    else if site == (HiddenSite.sectionStop w).info.id then some (w, false)
    else none

/-- `need_resched()` and `cond_resched()` in worker `self`, on the kernel's
    one CPU (`CONFIG_PREEMPT_NONE`): whether the kernel switched away, having
    run here what it ran. A scheduling choice, recorded: the kernel writes a
    resched record when `__cond_resched` is about to schedule. Then each
    following record that starts a crypt worker with queued work is that
    worker's run here (and so on, for what it switched to in turn). What the
    kernel ran that has no section (another task) leaves no other record;
    a worker the mirror cannot run here (a caller further up its stack)
    resumes later (`runWorker`). `fuel` bounds the nesting: each level is a
    worker run. -/
def condResched : Nat → Worker → M Bool
  | 0, _ => invariant "worker switches nested too deep"
  | fuel + 1, self => do
    let some site := self.resched? | invariant s!"{self.symbol} has no cond_resched"
    if (← peekHiddenSite) != some site.info.id then return false
    _ ← hidden site
    for _ in [0:16] do
      match (← peekHiddenSite).bind sectionOf with
      | some (.encryptWorker, true) =>
        if (← getDev).encryptQueue.isEmpty then break   -- not runnable: the record mismatches later
        runWorker .encryptWorker (WG.encryptWorker (condResched fuel .encryptWorker))
      | some (.txWorker, true) =>
        let some pid := (← getDev).txWorkQueue.head? | break
        modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.drop 1 }
        runWorker .txWorker (WG.txWorker pid (condResched fuel .txWorker))
      | _ => break
    -- the loop ends at a record it does not run; one it could run is a
    -- run beyond its bound
    match (← peekHiddenSite).bind sectionOf with
    | some (.encryptWorker, true) | some (.txWorker, true) =>
      if !(← getDev).encryptQueue.isEmpty || !(← getDev).txWorkQueue.isEmpty then
        invariant "more crypt worker runs at one cond_resched than the loop allows"
    | _ => pure ()
    modify fun s => { s with yieldedWorkers := s.yieldedWorkers ++ [self.index] }
    return true

/-- The bound on `condResched`'s nesting: a worker kind runs at most once
    per level on the modeled paths. -/
def SWITCH_DEPTH : Nat := 4

/-- The crypt work a deferred unit queued that has not run at one of its
    `cond_resched`s, on the kernel's one CPU after that unit: the encrypt
    worker (`packet_crypt_wq`, queued by `wg_packet_create_data`), then the
    tx worker of each peer it queued (`wg_queue_enqueue_per_peer_tx`),
    oldest first. What they send is delivered. -/
def runCryptWorkers : M Unit := do
  if !(← getDev).encryptQueue.isEmpty then
    runWorker .encryptWorker (WG.encryptWorker (condResched SWITCH_DEPTH .encryptWorker))
  for _ in [0:4096] do
    match (← getDev).txWorkQueue with
    | [] => deliverSent; return
    | pid :: rest =>
      modifyDev fun d => { d with txWorkQueue := rest }
      runWorker .txWorker (WG.txWorker pid (condResched SWITCH_DEPTH .txWorker))
      if !(← getDev).encryptQueue.isEmpty then invariant "the tx worker queued encryption"
  invariant "the tx work queue did not drain"

/-- Crypt work queued by a system call itself (a session's keepalive or
    staged packets sent from `wg_set` or `wg_xmit`): when the kworker runs it
    is not determined. -/
def requireNoCryptWork : M Unit := do
  let d ← getDev
  if !d.encryptQueue.isEmpty || !d.txWorkQueue.isEmpty then
    unsupported "crypt work queued in a system call (its worker's timing)"

/-- The handshake send worker for each queued peer, oldest first, once the
    queuing system call has returned: the guest waits inside every operation
    that can queue it (`wg_set`, `wg_up`, `wg_xmit`), and the worker's remote
    KCOV section lands in that operation. -/
def runSendWorkers : M Unit := do
  requireNoCryptWork
  modify fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  for _ in [0:4096] do
    match (← getDev).sendWorkQueue with
    | [] => deliverSent; return
    | pid :: rest =>
      modifyDev fun d => { d with sendWorkQueue := rest }
      let p ← getPeer pid
      if !p.handshakePending then invariant "queued work without a pending flag"
      setPeer pid { p with handshakePending := false }
      runWorker .sendWorker (WG.handshakeSendWorker pid)
  invariant "the send work queue did not drain"

/-- `wg_up` as the fixture performs it: once, on a port that is not the
    fixture's own, then `dev_change_flags` (the mirror's `wgUp`). -/
def wgUp : M Int := do
  let d ← getDev
  if d.running then unsupported "wg0 is already up (the fixture's routes exist)"
  if d.incomingPort == LISTEN_PORT then unsupported "wg0's port is the fixture's listener port"
  if d.incomingPort == SENDER_PORT then unsupported "wg0's port is the fixture's sender port"
  WG.wgUp

/-- `wg_observe`: its `recvfrom` on the IPv4 listener returns the first
    datagram there. The observation also lists every datagram both listeners
    hold, the datagrams the sender received, with their bytes (all drained),
    and wg0's transmit counters. Send work queued without a wait would run
    during the guest's wait before this operation, whose coverage is
    discarded: outside the domain. -/
def observe : M (Int × Lean.Json) := do
  if !(← getDev).sendWorkQueue.isEmpty then unsupported "send work queued by an operation that does not wait"
  requireNoCryptWork
  deliverSent
  let w ← get
  let hex (bs : List UInt8) : String := String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.mk [d[b.toNat / 16]!, d[b.toNat % 16]!])
  let type (bs : List UInt8) : Nat := WG.u32le bs 0
  let ret : Int := match w.listenerV4 with
    | bs :: _ => bs.length
    | [] => -EAGAIN
  let datagrams := (w.listenerV4.map fun bs => (4, bs)) ++ (w.listenerV6.map fun bs => (6, bs))
  let entries := datagrams.map fun (f, bs) => Lean.toJson [Lean.toJson f, Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (hex bs)]
  let replies := w.senderInbox.map fun dg => let bs := dg.bytes
    Lean.toJson [Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (if bs.length ≥ 12 then WG.u32le bs 8 else 0),
                 Lean.toJson (hex bs)]
  let sortJson (xs : List Lean.Json) := (xs.toArray.qsort fun a b => a.compress < b.compress).toList
  modify fun w => { w with listenerV4 := [], listenerV6 := [], senderInbox := [] }
  let d ← getDev
  return (ret, Lean.Json.mkObj [
    ("datagrams", Lean.Json.arr (sortJson entries).toArray),
    ("replies", Lean.Json.arr (sortJson replies).toArray),
    ("stats", Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped)])])

/-- wg0's addresses, added by the fixture at `wg_up` (`route_into_wg0`):
    `10.255.254.1/32` and `fd00:ffff::1/128`. -/
def WG0_ADDR4 : Nat := 0x0afffe01
def WG0_ADDR6 : Nat := 0xfd00ffff000000000000000000000001

/-- The IPv4 header checksum of `header` verifies (`ip_fast_csum` is 0). -/
def ipv4HeaderChecksumOk (header : List UInt8) : Bool :=
  let words := (List.range (header.length / 2)).map fun i => WG.beAt header (2 * i) 2
  let fold (n : Nat) := (n % 65536) + n / 65536
  fold (fold (fold (words.foldl (· + ·) 0))) == 0xffff

/-- The delivery of an inner packet that GRO flushed at `napi_complete_done`
    (a cut point: `gro_normal_list`, then the IPv4/IPv6 and UDP receive
    paths), decided fail-closed by an exact predicate
    (docs/2026-10-04-d2-data-plane.md, section 4). A delivered datagram is a
    UDP datagram to the fixture's sender (wg0's address, the sender's port,
    which is never wg0's own: `wgUp`); it lands in the sender's queue with
    its inner source. Everything else is outside the domain: stack replies
    (ICMP errors, other protocols), drops the environment does not model,
    options, extension headers and fragments.
    - IPv4: the UDP checksum is not verified, because wg marks the skb
      `CHECKSUM_UNNECESSARY`. A local source (wg0's address, loopback) is a
      martian and dropped by `ip_route_input_slow` / `fib_validate_source`.
    - IPv6: a local source is accepted, an asymmetry with IPv4; a zero UDP
      checksum is dropped (`udpv6_queue_rcv_one_skb`), a wrong nonzero one is
      delivered. -/
def deliverInner (pkt : List UInt8) : M Unit := do
  let byte (i : Nat) : Nat := (pkt.getD i 0).toNat
  let version := byte 0 / 16
  if version == 4 then
    if byte 0 % 16 != 5 then unsupported "an inner IPv4 packet with options"
    if !ipv4HeaderChecksumOk (pkt.take 20) then unsupported "an inner IPv4 header with a bad checksum"
    let totLen := WG.beAt pkt 2 2
    if totLen != pkt.length then invariant "consume_data_done trims to tot_len"
    if WG.beAt pkt 6 2 % 0x4000 != 0 then unsupported "an inner IPv4 fragment"
    if byte 9 != 17 then unsupported "an inner IPv4 packet other than UDP (the stack may reply)"
    let ulen := WG.beAt pkt 24 2
    if ulen != totLen - 20 || ulen < 8 then unsupported "an inner UDP length other than the IPv4 payload's"
    let src := WG.beAt pkt 12 4
    let dst := WG.beAt pkt 16 4
    if dst != WG0_ADDR4 || WG.beAt pkt 22 2 != SENDER_PORT then
      unsupported "an inner IPv4 datagram to another destination than the fixture's sender"
    -- martian sources: zeronet, loopback, multicast, class E and the limited
    -- broadcast; and wg0's own (local) address
    let top := src / 2 ^ 24
    if top == 0 || top == 127 || top ≥ 224 || src == WG0_ADDR4 then
      unsupported "an inner IPv4 datagram from a martian or local source"
    modify fun w => { w with senderInbox := w.senderInbox ++
      [{ family := AF_INET, addr := src, port := WG.beAt pkt 20 2, bytes := pkt.drop 28 }] }
  else if version == 6 then
    if byte 6 != 17 then unsupported "an inner IPv6 packet other than UDP, or with extension headers"
    let payloadLen := WG.beAt pkt 4 2
    if payloadLen + 40 != pkt.length then invariant "consume_data_done trims to the payload length"
    if WG.beAt pkt 44 2 != payloadLen || payloadLen < 8 then
      unsupported "an inner UDP length other than the IPv6 payload's"
    let src := WG.beAt pkt 8 16
    let dst := WG.beAt pkt 24 16
    if dst != WG0_ADDR6 || WG.beAt pkt 42 2 != SENDER_PORT then
      unsupported "an inner IPv6 datagram to another destination than the fixture's sender"
    -- unspecified, loopback, v4-mapped, link-local (a scope id) and multicast
    if src ≤ 1 || src / 2 ^ 32 == 0xffff || src / 2 ^ 118 == 0x3fa || src / 2 ^ 120 == 0xff then
      unsupported "an inner IPv6 datagram from an unspecified, loopback, mapped, link-local or multicast source"
    if WG.beAt pkt 46 2 == 0 then unsupported "an inner IPv6 UDP datagram with a zero checksum (dropped)"
    modify fun w => { w with senderInbox := w.senderInbox ++
      [{ family := AF_INET6, addr := src, port := WG.beAt pkt 40 2, bytes := pkt.drop 48 }] }
  else invariant "consume_data_done passed a packet that is neither IPv4 nor IPv6"

/-- The NET_RX softirq the decrypt worker's `napi_schedule` raised
    (`____napi_schedule` → `raise_softirq_irqoff` outside `net_rx_action`,
    which wakes ksoftirqd), placed by the records (design section 5). The
    hook is called at the worker's loop head and after its enqueue; it runs
    the poll iff a poll is pending and the next record starts a NET_RX
    section:
    - (a) ksoftirqd: the worker switched away at its `cond_resched` (a
      resched record, consumed by `condResched`, which stops at a NET_RX
      start), and ksoftirqd ran the softirq in a top-level section;
    - (b) inline: the worker's next `spin_unlock_bh` (`ptr_ring_consume_bh`)
      ran it, nested in the worker's section, with no resched record;
    - (c) an interrupt's exit ran it, nested, before or after the
      `need_resched()` test: the same records as (b), or a NET_RX section
      before a resched record.
    The placements differ only by the worker's state, which the poll does
    not read (the worker's remaining work is its next ring poll). Without
    records (the domain filter) the poll runs at the first hook. -/
def napiSoftirq : M Unit := do
  let d ← getDev
  let pending := d.peers.toList.filterMap fun (pid, p) => if p.napiScheduled then some pid else none
  if pending.isEmpty then return
  if (← get).hidden.isSome && (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  -- net_rx_action → napi_poll(n, &repoll) → n->poll(n, n->weight)
  runWorker .netRx do
    for pid in pending do
      discard <| WG.rxPoll pid WG.NAPI_POLL_WEIGHT fun pkts => pkts.forM deliverInner

/-- The decrypt worker (`packet_crypt_wq`, queued by `consume_data` in the
    injecting operation's NET_RX), once that softirq is done, with its
    NAPI softirq placement and its `cond_resched` (receive.c:505). -/
def runDecryptWorker : M Unit := do
  runWorker .decryptWorker (WG.decryptWorker napiSoftirq (condResched SWITCH_DEPTH .decryptWorker))
  if (← getDev).peers.toList.any (·.2.napiScheduled) then
    invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)"

/-- `wg_inject`: the fixture's sender sends one datagram to `port` on 127.0.0.1
    or ::1. Only wg0's own socket is in the domain: wg0 up, on that port.
    Loopback delivers it in softirq inside the `sendto`, and the guest waits
    for the handshake worker. -/
def inject (family port : Nat) (msg : List UInt8) : M Int := do
  let d ← getDev
  if !d.running || port != d.incomingPort then unsupported "a datagram to a port other than wg0's"
  -- a pending send worker inserts an index entry under a random index
  for pid in d.peerList do requireNotPending pid "receiving while a handshake is queued"
  fixtureSend
  let src ← senderSource family
  runWorker .netRx (WG.wgReceive msg src)
  -- the queued receive work runs before the guest's wait ends
  if !(← getDev).handshakeQueue.isEmpty then
    runWorker .receiveWorker (WG.handshakeReceiveWorker (discard <| condResched SWITCH_DEPTH .receiveWorker))
  -- or the decrypt worker, with the NAPI poll its packet schedules
  if !(← getDev).decryptQueue.isEmpty then runDecryptWorker
  -- then the crypt work the receive worker or the NAPI poll queued (a
  -- session's keepalive, staged packets on key confirmation)
  runCryptWorkers
  deliverSent
  return msg.length   -- udp_sendmsg returns the datagram's length

end Leanux.Env
