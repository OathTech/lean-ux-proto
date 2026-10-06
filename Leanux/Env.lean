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
- the fixture's bound ports (`portBound`) and its routes into wg0
  (`World.routesViaWg0`), which `wg_up`, `wg_down` and `wg_delete` change
  (docs/2026-10-05-l-lifecycle.md, section 5);
- when the kworkers run: the handshake receive worker inside `wg_inject`,
  then the encrypt and tx workers it queued, and the (mirrored) handshake
  send worker at the end of the operation that queued it, which the guest
  waits for; the encrypt and tx workers `wg_xmit` queued, after it
  (`afterXmit`);
- the IP packet the fixture's sender hands `wg_xmit` (`xmitPacket`) and the
  checksum completion `encrypt_packet` asks of the stack (`checksumHelp`);
- where wg0's datagrams go over loopback, and how the sender's `recvfrom`
  reports their source.
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- The fixture's UDP listeners are on 127.0.0.1 and ::1 at this port. -/
def LISTEN_PORT : Nat := 51999

/-- The fixture's sender (`wg_inject`) is bound to this port on `[::]`
    (dual-stack); `wg_observe` drains what it received. -/
def SENDER_PORT : Nat := 51998

/-- L (docs/2026-10-05-l-lifecycle.md, section 2.3): the ports where a
    wildcard UDP bind of wg0's conflicts with a fixture socket (no
    `SO_REUSEADDR`; a wildcard address matches any): the `127.0.0.1`
    listener's and the dual-stack `[::]` sender's. The `::1` listener is
    `v6only` at `LISTEN_PORT`, already excluded by the IPv4 bind. -/
def portBound (p : Nat) : Bool := p == LISTEN_PORT || p == SENDER_PORT

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
      -- from wg0's socket, bound to the wildcard address at its port: over
      -- loopback the source is the destination's own address
      let src := { family := dg.family, addr := dg.addr, port := dg.sport, bytes := dg.bytes : InboxDatagram }
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
        runWorker .encryptWorker (WG.encryptWorker checksumHelp (condResched fuel .encryptWorker))
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
    runWorker .encryptWorker (WG.encryptWorker checksumHelp (condResched SWITCH_DEPTH .encryptWorker))
  for _ in [0:4096] do
    match (← getDev).txWorkQueue with
    | [] => deliverSent; return
    | pid :: rest =>
      modifyDev fun d => { d with txWorkQueue := rest }
      runWorker .txWorker (WG.txWorker pid (condResched SWITCH_DEPTH .txWorker))
      if !(← getDev).encryptQueue.isEmpty then invariant "the tx worker queued encryption"
  invariant "the tx work queue did not drain"

/-- Crypt work queued by a system call itself (a session's keepalive or
    staged packets sent from `wg_set` or `wg_up`): when the kworker runs it
    is not determined, since these operations' waits are not measured for
    it. `wg_xmit` has its own (`afterXmit`). -/
def requireNoCryptWork : M Unit := do
  let some d := (← getK).wg | return
  if !d.encryptQueue.isEmpty || !d.txWorkQueue.isEmpty then
    unsupported "crypt work queued in a system call (its worker's timing)"

/-- The handshake send worker for each queued peer, oldest first, once the
    queuing system call has returned: the guest waits inside every operation
    that can queue it (`wg_set`, `wg_up`, `wg_xmit`), and the worker's remote
    KCOV section lands in that operation. -/
def runSendWorkers : M Unit := do
  if (← getK).wg.isNone then return   -- L: no device, no worker
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

/-- After `wg_xmit` returns: the guest waits `QUEUE_WAIT_US` (0.1 s), in
    which the kworkers run what the call queued: the encrypt worker and the
    tx worker (`runCryptWorkers`, ordered by their section records, with the
    loopback delivery of what they send), or the handshake send worker
    (`runSendWorkers`). A call that queued both (a session and no session at
    once) does not occur on the modeled paths; their order would be
    unrecorded here, so it is outside the domain. The section records, and
    the guest's opened-section count, show a worker that outlived the wait:
    its records would be missing from this operation. -/
def afterXmit : M Unit := do
  let some d := (← getK).wg | return   -- L: no device (the send failed)
  let crypt := !d.encryptQueue.isEmpty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    unsupported "wg_xmit queued crypt work and a handshake (their order)"
  modify fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  if crypt then runCryptWorkers
  runSendWorkers

/-! ## D3: timers and the time advance (docs/2026-10-05-d3-timers.md, section 5.3)

Interface stubs, owned by stream M: the hooks exist and stop
`unsupported "D3 stream M: not yet ..."` where the semantics belong to M. -/

/-- The site of the next record that is not ambient and not a pending
    section stop, without consuming anything (unlike `peekHiddenSite`). -/
def peekNextSite : M (Option Nat) := do
  let w ← get
  let some rs := w.hidden | return none
  let ambient := HiddenSite.all.filter (·.info.role == .ambient) |>.map (·.info.id)
  let rec go : List HiddenRecord → List Nat → Option Nat
    | r :: rest, pending =>
      if ambient.contains r.site then go rest pending
      else if pending.contains r.site then go rest (pending.erase r.site)
      else some r.site
    | [], _ => none
  return go rs w.pendingStops

/-- The D3 unit whose section a record starts: a timer callback or the
    clear worker. -/
def timerSectionOf (site : Nat) : Option Worker :=
  Worker.all.find? fun w =>
    (w.timer?.isSome || w == .clearPeerWorker) && site == (HiddenSite.sectionStart w).info.id

/-- A timer callback's section, run by the environment (`call_timer_fn`):
    noted for the trace's `fired:<symbol>` expectations, then run as any
    dispatched unit. The caller (stream M) has chosen the peer and cleared
    its timer: the callback is entered with its own timer detached. -/
def runTimerSection (w : Worker) (body : M Unit) : M Unit := do
  if w.timer?.isNone then invariant s!"{w.symbol} is not a timer callback"
  modify fun s => { s with fired := s.fired.push w.symbol }
  runWorker w body

/-- An idle point (the guest's waits after `wg_set`, `wg_up`, `wg_inject`,
    `wg_xmit`, and before `wg_observe`), where a timer may fire naturally.
    Stub: a timer or clear-worker section here is not yet modeled. Reads no
    state and consumes nothing. -/
def idleTimers : M Unit := do
  if let some w := (← peekNextSite).bind timerSectionOf then
    unsupported s!"D3 stream M: not yet (the section of {w.symbol} at an idle point)"

/-- `wg_advance`: `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)` on the
    trace's KCOV descriptor, then the guest's wait (stream K, section 13.3).
    Stub: the kind-304 record (`.timeAdvance`, `{before, after}`), the
    timer sections the next tick runs and the work they queue belong to
    stream M. The ioctl returns 0. -/
def advance (ticks : Nat) : M Int :=
  unsupported s!"D3 stream M: not yet (wg_advance of {ticks} ticks: the kind-304 record and the timers it fires)"

/-- Work a down or a deletion would leave behind: crypt work (its worker's
    timing) and a decrypt queue or NAPI poll still pending
    (docs/2026-10-05-l-lifecycle.md, section 9). -/
def requireIdleDevice : M Unit := do
  requireNoCryptWork
  let d ← getDev
  if !d.decryptQueue.isEmpty || d.peers.toList.any (·.2.napiScheduled) then
    unsupported "receive work queued at wg_stop (its worker's timing)"

/-- `wg_up`: `SIOCSIFFLAGS` with `IFF_UP` (`dev_ifsioc`, `dev_change_flags`).
    Without wg0, `-ENODEV` (`dev_load` requests no module: no
    `CONFIG_MODULES`). An up device does not change (`__dev_change_flags`
    sees no `IFF_UP` change, dev.c:8962). Otherwise the mirror's `wgUp`;
    after a success the guest adds wg0's addresses and routes. -/
def wgUp : M Int := do
  let some d := (← getK).wg | return -ENODEV
  if d.running then return 0
  let ret ← WG.wgUp
  if ret == 0 then modify fun w => { w with routesViaWg0 := true }
  return ret

/-- `wg_down`: `SIOCSIFFLAGS` without `IFF_UP`. `-ENODEV` without wg0; a
    down device does not change; an up one goes through `__dev_close_many`
    (`wg_stop`), and `NETDEV_DOWN` removes the routes. -/
def wgDown : M Int := do
  let some d := (← getK).wg | return -ENODEV
  if !d.running then return 0
  requireIdleDevice
  WG.wgDown
  modify fun w => { w with routesViaWg0 := false }
  return 0

/-- `wg_delete`: `RTM_DELLINK` (the mirror's `wgDelete`); `NETDEV_DOWN` and
    `NETDEV_UNREGISTER` remove every route via wg0. -/
def wgDelete : M Int := do
  if (← getK).wg.isSome then requireIdleDevice
  let ret ← WG.wgDelete
  modify fun w => { w with routesViaWg0 := false }
  return ret

/-- `wg_observe`: its `recvfrom` on the IPv4 listener returns the first
    datagram there. The observation also lists every datagram both listeners
    hold, the datagrams the sender received, each with its `recvfrom`
    source (family, address, port) and bytes (all drained), and wg0's
    transmit counters and receive error counters (`rx_errors` moves with one
    of these, so it adds nothing). Send work queued without a wait would run
    during the guest's wait before this operation, whose coverage is
    discarded: outside the domain. -/
def observe : M (Int × Lean.Json) := do
  idleTimers   -- the guest's wait before this operation
  if let some d := (← getK).wg then
    if !d.sendWorkQueue.isEmpty then unsupported "send work queued by an operation that does not wait"
  requireNoCryptWork
  deliverSent
  let w ← get
  let hex (bs : List UInt8) : String := String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.mk [d[b.toNat / 16]!, d[b.toNat % 16]!])
  -- the guest reports type 0 for a datagram shorter than 4 bytes
  let type (bs : List UInt8) : Nat := if bs.length ≥ 4 then WG.u32le bs 0 else 0
  let ret : Int := match w.listenerV4 with
    | bs :: _ => bs.length
    | [] => -EAGAIN
  let datagrams := (w.listenerV4.map fun bs => (4, bs)) ++ (w.listenerV6.map fun bs => (6, bs))
  let entries := datagrams.map fun (f, bs) => Lean.toJson [Lean.toJson f, Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (hex bs)]
  -- the sender's `recvfrom` source: a `sockaddr_in6` (SEND_FD is an IPv6
  -- socket), where an IPv4 source appears v4-mapped (::ffff:a.b.c.d)
  let replies := w.senderInbox.map fun dg => let bs := dg.bytes
    let addr6 := if dg.family == AF_INET then 0xffff00000000 + dg.addr else dg.addr
    Lean.toJson [Lean.toJson AF_INET6, Lean.toJson (hex (beBytes addr6 16)), Lean.toJson dg.port,
                 Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (if bs.length ≥ 12 then WG.u32le bs 8 else 0),
                 Lean.toJson (hex bs)]
  let sortJson (xs : List Lean.Json) := (xs.toArray.qsort fun a b => a.compress < b.compress).toList
  modify fun w => { w with listenerV4 := [], listenerV6 := [], senderInbox := [] }
  -- L: without wg0 the guest's RTM_GETLINK fails with ENODEV: `stats` null
  let stats := match (← getK).wg with
    | some d => Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped),
                                 ("rx_frame_errors", Lean.toJson d.rxFrameErrors),
                                 ("rx_length_errors", Lean.toJson d.rxLengthErrors)]
    | none => Lean.Json.null
  return (ret, Lean.Json.mkObj [
    ("datagrams", Lean.Json.arr (sortJson entries).toArray),
    ("replies", Lean.Json.arr (sortJson replies).toArray),
    ("stats", stats)])

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
    -- ip_fast_csum of the header
    if onesSum (pkt.take 20) != 0xffff then unsupported "an inner IPv4 header with a bad checksum"
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
    -- broadcast; and wg0's own (local) address. Environment facts behind this
    -- set (fixture state, not C): rp_filter = 0 and accept_local = 0, no
    -- local routes beyond the fixture's, and the only local IPv4 addresses
    -- are 127.0.0.1 and wg0's (`fib_validate_source` drops a local source).
    -- A fixture change shows as an inbox mismatch.
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
  let some d := (← getK).wg | unsupported "a datagram to a port other than wg0's (no wg0)"
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

/-- `wg_flood` (docs/2026-10-05-e-dos.md §8): the fixture submits an io_uring
    batch of invalid-MAC1 initiations to wg0's port. On the kernel they cross the
    `handshake_queue_len >= 512` threshold, set `last_under_load`, and are all
    dropped at the MAC1 check (reply-free), in one fully-drained receive-worker
    section. The mirror does not model the flood's scheduling-driven dynamics:
    it discards the whole flood section's records (§4.1) and records only that
    `under_load` was set. It requires the flood to have reached the receive
    worker and crossed the threshold (an `.under_load_now` record); a flood that
    did not cross, or whose section did not close in this operation (the worker
    outliving the window, a merged injection — §4.1), fails closed. The op
    returns 0 (the submission succeeded). -/
def flood (count port : Nat) (messages : List (List UInt8)) : M Int := do
  let some d := (← getK).wg | unsupported "a flood to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a flood to a port other than wg0's"
  -- without records (the domain filter runs before Linux), accept the flood: it
  -- is a natural harness input, inside the domain
  if (← get).hidden.isNone then
    modify fun w => { w with lastUnderLoad := some 0 }
    return 0
  let startW := (HiddenSite.sectionStart .receiveWorker).info.id
  let stopW := (HiddenSite.sectionStop .receiveWorker).info.id
  let startRx := (HiddenSite.sectionStart .netRx).info.id
  let stopRx := (HiddenSite.sectionStop .netRx).info.id
  let cuts := [startRx, stopRx, (HiddenSite.ipIdentKey).info.id, (HiddenSite.ipIdentReserve).info.id,
               (HiddenSite.flowHashSecret).info.id, (HiddenSite.udpPortDraw).info.id]
  -- before the receive worker runs: the fixture's io_uring sends' producer
  -- `net_rx` sections and IP-layer cut draws
  let _ ← discardFloodRecords startW cuts
  -- the receive-worker section: the checked leading valid packets first, then
  -- the invalid flood discarded
  _ ← hidden (.sectionStart .receiveWorker)
  modify fun w => { w with floodDepth := count + messages.length }
  let src ← senderSource 4
  for msg in messages do
    WG.receiveHandshakePacket msg src    -- under load via the queue depth; its
                                         -- records (under_load, make_cookie ×2,
                                         -- nonce, reply) are consumed in order
  modify fun w => { w with floodDepth := 0 }
  -- the remaining invalid packets' per-packet reads (under_load / decay /
  -- reschedule), discarded; a modeled record here (a mid-flood injection) fails
  let (_, crossed) ← discardFloodRecords stopW
    ([(HiddenSite.underLoadNow).info.id, (HiddenSite.birthdateExpired).info.id,
      (HiddenSite.reschedReceive).info.id] ++ cuts)
  _ ← hidden (.sectionStop .receiveWorker)
  if messages.isEmpty && !crossed then
    throw (.hidden "the flood did not cross the under_load threshold (no under_load record)")
  deliverSent
  return 0

end Leanux.Env
