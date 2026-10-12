import Leanux.WG.Device
import Leanux.WG.Receive
import Leanux.WG.Data
import Leanux.WG.RxData
import Leanux.WG.Timers
import Leanux.Env.IpStack
import Leanux.Env.Batch
import Leanux.Env.Stack

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

Since the interface commit (docs/2026-10-11-interface.md) two parts live in
their own files, each owned by one W4+W7 stream: the transmit-side IP stack
(`Leanux/Env/IpStack.lean`: `xmitPacket`, `checksumHelp`, the ports and
addresses the packets carry) and the deferred units' shared machinery
(`Leanux/Env/Batch.lean`: `runWorker`, `sectionOf`, `condResched`). This
file keeps the fixture, the operations, the worker runners, the timers and
the lifecycle: the hooks the streams meet at.
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- The fixture's UDP listeners are on 127.0.0.1 and ::1 at this port. -/
def LISTEN_PORT : Nat := 51999

/-- L (docs/2026-10-05-l-lifecycle.md, section 2.3): the ports where a
    wildcard UDP bind of wg0's conflicts with a fixture socket (no
    `SO_REUSEADDR`; a wildcard address matches any): the `127.0.0.1`
    listener's and the dual-stack `[::]` sender's. The `::1` listener is
    `v6only` at `LISTEN_PORT`, already excluded by the IPv4 bind. -/
def portBound (p : Nat) : Bool := p == LISTEN_PORT || p == SENDER_PORT

/-- W5 (docs/2026-10-06-w5-w6-receive.md, 2.5): the link-local address on
    `lo`, fe80::ffff:1/128 (harness/guest.c `network_fixture`; not fe80::1,
    which existing traces transmit to through wg0), the source of a
    `from: "ll"` injection (`IPV6_PKTINFO` on the dual-stack sender: the
    address and interface 1). -/
def LO_LINK_LOCAL : Nat := 0xfe8000000000000000000000ffff0001

/-- W1 (docs/2026-10-06-w1-w2-netlink.md, 2.1): the fixture namespace's
    devices besides wg0, for `lookup_interface`: `lo` (ifindex 1, no
    `rtnl_link_ops`, drivers/net/loopback.c) and `sit0` (ifindex 2, kind
    "sit": the per-netns fallback device of `CONFIG_IPV6_SIT=y`,
    net/ipv6/sit.c:1852-1860). wg0 is created third (ifindex 3; L's cursor
    gives 4 after a delete and re-create). -/
def fixtureNetDevices : List (String × Nat × Option String) := [("lo", 1, none), ("sit0", 2, some "sit")]

/-- Whether an endpoint is the fixture's sender: its port at the loopback
    addresses, or (W5) at the link-local address on `lo` (the sender is
    bound to `[::]`, so a datagram to `fe80::1` at its port reaches it). -/
def isSender (family addr port : Nat) : Bool :=
  port == SENDER_PORT && ((family == AF_INET && addr == 0x7f000001)
    || (family == AF_INET6 && (addr == 1 || addr == LO_LINK_LOCAL)))

/-- What the sender's datagrams carry in their skb: loopback source and
    destination, the sender's port, the loopback interface (ifindex 1), and
    the DS field the operation's `tos` set on the sender (W5, 2.1: `IP_TOS`
    for a v4-mapped destination, `IPV6_TCLASS` otherwise, ECN bits kept).
    With `ll` (W5, 2.5) the source is the link-local address on `lo`
    (`IPV6_PKTINFO`), the destination still `::1`. -/
def senderSource (family : Nat) (tos : Nat := 0) (ll : Bool := false) : M SkbSource :=
  if family == 4 then
    if ll then unsupported "a link-local source for an IPv4 injection"
    else pure { family := 4, saddr := 0x7f000001, sport := SENDER_PORT, daddr := 0x7f000001, iif := 1, tos }
  else if family == 6 then
    pure { family := 6, saddr := if ll then LO_LINK_LOCAL else 1, sport := SENDER_PORT, daddr := 1, iif := 1, tos }
  else unsupported "an injection family other than IPv4 or IPv6"

/-- The guest waits `OBSERVE_WAIT_US` (0.4 s) after every injection, and
    fails any trace that runs longer than `REKEY_BOUND_NS` (4.5 s) after
    the start of its `wg_up`, net of its advances (D3). So two consumed
    initiations are at least 0.4 s apart (and the first comes long after
    boot). The bound gives the D3 firing window's `traceBound`. -/
def INJECT_GAP_NS : Nat := 400000000
def TRACE_BOUND_MS : Nat := 4500

/-- D3 (docs/2026-10-05-d3-timers.md, section 5.3): the firing window's
    bounds. The guest waits `ADVANCE_WAIT_US` (0.1 s, 25 ticks) once an
    advance is absorbed (stream K, section 13.3), and the trace's real-time
    bound is 4.5 s from just before `wg_up` (`TRACE_BOUND_MS`, 1125 ticks),
    net of the advances. -/
def timing : Timing where
  advanceWait := 25
  traceBound := TRACE_BOUND_MS * WG.HZ / 1000

/-- The fixture's own `sendto` (into wg0's route, or to wg0's port): the IP
    output path draws the ident key and the ident, and may initialize the
    flow-hash secret; these are cut-site choices (choice-stream strategy,
    section 5). -/
def fixtureSend : M Unit :=
  -- and the datagram's skb (`sock_alloc_send_pskb`, an allocation cut site)
  skipCut ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts)

/-- The fixture's `sendto` into wg0's route, to a multicast destination,
    before `wg_xmit`: the IP output loops a copy back to local receivers.
    - IPv4: the route of any multicast destination is `RTCF_MULTICAST`, and
      `sk_mc_loop` holds (the sender is an IPv6 socket, whose
      `IPV6_MULTICAST_LOOP` defaults to on), so `ip_mc_output` clones the
      packet to `ip_mc_finish_output` → `dev_loopback_xmit` → `netif_rx`
      before `ip_finish_output` hands it to wg0 (ip_output.c:382-424).
      `netif_rx` disables bottom halves around the enqueue and its
      `local_bh_enable` runs the raised NET_RX (dev.c:5374-5387): a
      section of its own (`WG.loopbackSend`). No socket takes the copy
      (none is bound to `SEND_PORT`), and a multicast is not answered with
      an ICMP error.
    - IPv6: `ip6_finish_output2` loops a copy only to a group wg0 has
      joined (`ipv6_chk_mcast_addr`), which the environment does not model.
    Recorded evidence: every `wg_xmit` to 224.0.0.1 shows one NET_RX section
    and no other record (41 operations, 2026-10-06), which the lax cut of
    `wg_xmit`'s error path used to absorb. -/
def xmitMulticastLoop (family addr : Nat) : M Unit := do
  -- W4 (section 2.4): the IPv4 copy loops only for a joined group, `224.0.0.1`
  -- (`multicastLoops`); another IPv4 group is sent out without a copy
  if multicastLoops family addr then WG.loopbackSend [] true
  else if family == 6 && addr / 2 ^ 120 == 0xff then
    unsupported "an IPv6 multicast destination (whether the IP output loops a copy back depends on wg0's groups)"

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
    let loopback := (dg.family == AF_INET && dg.addr / 2 ^ 24 == 127)
      || (dg.family == AF_INET6 && (dg.addr == 1 || dg.addr == LO_LINK_LOCAL))
    -- W1 hand-off to W9: a datagram to an IPv6 endpoint with a nonzero
    -- `sin6_scope_id` routes with `flowi6_oif` set (`send6`), which the
    -- environment does not model; a v4-mapped destination is not loopback
    -- and falls to the rule below. The endpoint is the peer's.
    if dg.family == AF_INET6 then
      if let some d := (← getK).wg then
        for pid in d.peerList do
          if let some e := (← getPeer pid).endpoint then
            if e.family == AF_INET6 && e.addr == dg.addr && e.port == dg.port && e.scope != 0 then
              unsupported "a datagram to a scoped IPv6 endpoint (send6's route lookup, W9)"
    if isSender dg.family dg.addr dg.port then
      -- from wg0's socket, bound to the wildcard address at its port, with
      -- the source `send4`/`send6` ask for: the endpoint's `src4`/`src6`
      -- (the destination of the datagram it was learned from, a local
      -- address here, socket.c:134-135), or, for an endpoint set by
      -- netlink, the route's choice: over loopback the destination's own
      -- address (W5, 2.5). The outer DS field is `ds` (W5, 2.1).
      -- the destination `IPV6_PKTINFO` reports on the dual-stack socket: an
      -- IPv4 datagram's as v4-mapped (ip6_datagram_recv_common_ctl)
      let src := { family := dg.family, addr := if dg.src != 0 then dg.src else dg.addr, port := dg.sport,
                   bytes := dg.bytes, tos := dg.ds,
                   dst := if dg.family == AF_INET6 then dg.addr else 0xffff00000000 + dg.addr : InboxDatagram }
      modify fun w => { w with senderInbox := w.senderInbox ++ [src] }
    else match listenerFamily { family := dg.family, addr := dg.addr, port := dg.port } with
      | some 4 => modify fun w => { w with listenerV4 := w.listenerV4 ++ [(dg.ds, dg.bytes)] }
      | some _ => modify fun w => { w with listenerV6 := w.listenerV6 ++ [(dg.ds, dg.bytes)] }
      | none => if !loopback then unsupported "a datagram routed back into wg0"
  modify fun w => { w with sent := [] }

/-- The crypt work a deferred unit queued that has not run at one of its
    `cond_resched`s, on the kernel's one CPU after that unit: the encrypt
    worker (`packet_crypt_wq`, queued by `wg_packet_create_data`), then the
    tx worker of each peer it queued (`wg_queue_enqueue_per_peer_tx`),
    oldest first. What they send is delivered. -/
def runCryptWorkers (runDecrypt : M Unit := unsupported "a switch to the decrypt worker at this point (its placement is not modeled here)") : M Unit := do
  if !(← getDev).encryptQueue.isEmpty then
    runWorker .encryptWorker (WG.encryptWorker checksumHelp (condResched SWITCH_DEPTH .encryptWorker runDecrypt))
  for _ in [0:4096] do
    let d ← getDev
    match d.txWorkQueue.head? with
    | none => deliverSent; return
    | some headPid =>
      -- the tx worker the dispatch record names (dispatch order), else the head
      let pid ← match ← peekUnit .txWorker with
        | some u => resolveUnit .txWorker u d.txWorkQueue
        | none => pure headPid
      modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.erase pid }
      runWorker .txWorker (WG.txWorker pid (condResched SWITCH_DEPTH .txWorker runDecrypt)) (some pid)
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

/-- The handshake send worker whose unit the next dispatch record names
    (docs/2026-10-11-dispatch-order.md: `handshake_send_wq` is unbound, so
    two queued items may run in either order), or, without an identity (the
    domain filter's placeholders), the peer at the head of the queue. -/
def runOneSendWorker : M Unit := do
  let d ← getDev
  let some headPid := d.sendWorkQueue.head? | invariant "no queued handshake send work"
  let pid ← match ← peekUnit .sendWorker with
    | some u => resolveUnit .sendWorker u d.sendWorkQueue
    | none => pure headPid
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue.erase pid }
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid { p with handshakePending := false }
  runWorker .sendWorker (WG.handshakeSendWorker pid)

/-- The handshake send worker for each queued peer, oldest first, once the
    queuing system call has returned: the guest waits inside every operation
    that can queue it (`wg_set`, `wg_up`, `wg_xmit`), and the worker's remote
    KCOV section lands in that operation. -/
def runSendWorkers : M Unit := do
  if (← getK).wg.isNone then return   -- L: no device, no worker
  requireNoCryptWork
  modify fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  for _ in [0:4096] do
    if (← getDev).sendWorkQueue.isEmpty then deliverSent; return
    runOneSendWorker
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

Timer sections are accepted at the idle points, where the guest sleeps:
inside `wg_advance`'s wait and in the waits after `wg_set`, `wg_up`,
`wg_inject`, `wg_xmit` and before `wg_observe`. Which timers fired, and in
what order, is captured by their sections; a section is accepted iff its
timer is pending and could be due (`fireTimer`). A timer section anywhere
else is a hidden mismatch: the mirror cannot run a callback mid-body. -/

/-- The site of the next record that is not ambient and not a pending
    section stop, without consuming anything (unlike `peekHiddenSite`). -/
def peekNextSite : M (Option Nat) := do
  let w ← get
  let some rs := w.hidden | return none
  let rec go : List HiddenRecord → List Nat → Option Nat
    | r :: rest, pending =>
      if HiddenSite.passive r.site then go rest pending   -- ambient, or a queue record
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

/-- The clear work (`wg_queued_expired_zero_key_material`) of the peer at
    the head of its queue. It shares `handshake_send_wq` with the send
    worker; their order is the records' (a captured scheduling choice). -/
def runOneClearWorker : M Unit := do
  let d ← getDev
  let some headPid := d.clearWorkQueue.head? | invariant "no queued clear work"
  let pid ← match ← peekUnit .clearPeerWorker with
    | some u => resolveUnit .clearPeerWorker u d.clearWorkQueue
    | none => pure headPid
  modifyDev fun d => { d with clearWorkQueue := d.clearWorkQueue.erase pid }
  runWorker .clearPeerWorker (WG.queuedExpiredZeroKeyMaterial pid)

/-- The timer callback that serves timer `t`. -/
def timerWorker (t : PeerTimer) : M Worker := do
  match Worker.all.find? (·.timer? == some t) with
  | some w => return w
  | none => invariant "a peer timer without a callback unit"

/-- `call_timer_fn` of callback `w`, whose section the next record starts.
    The start record names the timer (its address, from the arm record:
    docs/2026-10-11-dispatch-order.md), which must be of that callback's
    kind, pending and due: `expires < jHi` (a timer fires no earlier than
    `expires + 1`, by a softirq whose `jiffies` is at most `jHi`). So several
    peers' timers of one kind due in one pass run in the order the records
    show (W12, docs/2026-10-06-w3-w12.md Part II: the wheel's order is
    `bucket_expiry` ascending, higher level first at one step, LIFO within a
    bucket, which the records carry and the mirror need not reconstruct).
    Without a name (the domain filter's placeholders) exactly one due peer
    is taken; several stay outside that prediction. A section with no due
    timer is a hidden mismatch. The timer is detached before the call
    (`expire_timers`, timer.c:1828-1829). -/
def fireTimer (w : Worker) (jHi : Nat) : M Unit := do
  let some t := w.timer? | invariant s!"{w.symbol} is not a timer callback"
  let d ← getDev
  let due := d.peerList.filter fun pid =>
    match d.peers.get? pid >>= (·.timer t) with
    | some e => e < jHi
    | none => false
  -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
  -- section names, by the address its arm record carried
  let named ← match ← peekUnit w with
    | some u =>
      match (← get).timerUnits.find? (·.1 == u) with
      | some (_, pid, t') =>
        if t' != t then throw (.hidden s!"a section of {w.symbol} for another timer of peer {pid}")
        pure (some pid)
      | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
    | none => pure none
  match named with
  | some pid =>
    if !due.contains pid then
      throw (.hidden s!"a section of {w.symbol} for peer {pid}, whose timer is not pending with expires before jiffies {jHi}")
    delTimer pid t
    runTimerSection w (WG.timerCallback pid t)
  | none =>
    match due with
    | [pid] =>
      delTimer pid t
      runTimerSection w (WG.timerCallback pid t)
    | [] => throw (.hidden s!"a section of {w.symbol}, but no peer's timer is pending with expires before jiffies {jHi}")
    | _ => unsupported s!"several peers' timers for {w.symbol} due in one pass (their order)"

/-- The timer sections the records show at an idle point, and the work they
    queue, in record order (docs/2026-10-05-d3-timers.md, section 5.3):
    `call_timer_fn` of each due timer (`fireTimer`), then the handshake send
    worker and the clear work (FIFO on `handshake_send_wq`, ordered by
    their records), the encrypt and tx workers, and the loopback delivery
    of what they send. Work queued before the idle point has run already
    (each operation runs its own); a worker section here without queued
    work is left to the caller, whose records then mismatch. Whether a
    timer fired. Work a timer queued that has not run when the records end
    outlived the guest's wait: outside the domain. Without records (the
    domain filter) nothing fires here. -/
def runTimers (jHi : Nat) : M Bool := do
  modify fun w => { w with queuedThisCall := [] }   -- the guest slept
  -- L: without wg0 (bare fixture, or after wg_delete) no WireGuard timer
  -- exists; a timer section in the records stays unconsumed and mismatches
  -- [AGENT, int-dl merge]
  if (← getK).wg.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  for _ in [0:4096] do
    let some site ← peekNextSite | break
    let d ← getDev
    if let some w := timerSectionOf site then
      if w == .clearPeerWorker then
        if d.clearWorkQueue.isEmpty then break
        runOneClearWorker
      else
        fireTimer w jHi
        fired := true
    else if !fired then break
    else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorker
    else if (site == startOf .encryptWorker || site == startOf .txWorker)
        && (!d.encryptQueue.isEmpty || !d.txWorkQueue.isEmpty) then runCryptWorkers
    else break
  if fired then
    deliverSent
    let d ← getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.isEmpty || !d.txWorkQueue.isEmpty then
      unsupported "work a timer queued outlived the guest's wait"
  return fired

/-- The domain filter's stand-in for an advance's timer pass (no records):
    every pending timer with `expires < jHi` fires, earliest first (bucket
    order), then the crypt workers, the send workers and the clear work. A
    prediction for the filter's verdict only; the check follows the
    records. -/
def runTimersPlaceholder (jHi : Nat) : M Unit := do
  modify fun w => { w with queuedThisCall := [] }
  if (← getK).wg.isNone then return   -- L: no wg0, no timers [AGENT, int-dl merge]
  for _ in [0:64] do
    let d ← getDev
    let due := d.peerList.flatMap fun pid =>
      match d.peers.get? pid with
      | some p => PeerTimer.all.filterMap fun t => (p.timer t).bind fun e => if e < jHi then some (e, pid, t) else none
      | none => []
    let first := due.foldl (fun acc c => match acc with
      | some a => if c.1 < a.1 then some c else some a
      | none => some c) none
    let some (_, pid, t) := first | break
    delTimer pid t
    runTimerSection (← timerWorker t) (WG.timerCallback pid t)
  runCryptWorkers
  runSendWorkers
  for _ in [0:64] do
    if (← getDev).clearWorkQueue.isEmpty then break
    runOneClearWorker

/-- An idle point (the guest's waits after `wg_set`, `wg_up`, `wg_inject`,
    `wg_xmit`, and before `wg_observe`), where a timer may fire naturally:
    `jiffies` is at most the last recorded one plus the trace's real-time
    bound plus a wait (`Timing`). -/
def idleTimers : M Unit := do
  let w ← get
  discard <| runTimers (w.jiffiesLast.getD 0 + w.timing.traceBound + w.timing.advanceWait)

/-- `wg_advance`'s ioctl: `leanux_time_advance` moves `jiffies_64` by
    `ticks` (`do_timer`), and the ioctl records kind 304 `{before, after}`
    (`.timeAdvance`) and returns 0. The record must show exactly `ticks`;
    `after` becomes the last known `jiffies`. The window rule needs every
    pending timer's recorded expiry, so with records but without arm records
    an advance is outside the domain. Without records (the domain filter)
    the advance starts from the last known `jiffies` (0 before any). -/
def advance (ticks : Nat) : M Int := do
  let w ← get
  let (j0, j1) ← if w.hidden.isNone && w.hiddenPlaceholders then
      let j0 := w.jiffiesLast.getD 0
      pure (j0, j0 + ticks)
    else do
      if !w.armRecords then unsupported "a time advance without arm records (the timers' expiries are unknown)"
      let bs ← hidden .timeAdvance
      pure (WG.recordWord bs 0, WG.recordWord bs 1)
  if j1 < j0 || j1 - j0 != ticks then
    throw (.hidden s!"the advance moved jiffies from {j0} to {j1}, not by {ticks}")
  modify fun w => { w with jiffiesLast := some j1 }
  return 0

/-- The guest's wait after `wg_advance`'s ioctl (stream K, section 13.3: until
    the monotonic clock has absorbed the advance, then `ADVANCE_WAIT_US`):
    the next tick raises `TIMER_SOFTIRQ`, the due callbacks run in sections,
    then the work they queue, all in this operation's records. -/
def afterAdvance : M Unit := do
  let w ← get
  let jHi := w.jiffiesLast.getD 0 + w.timing.advanceWait
  if w.hidden.isNone && w.hiddenPlaceholders then runTimersPlaceholder jHi
  else discard <| runTimers jHi

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
  -- `dev_change_flags`' rtnetlink notifications and the fixture's routes
  -- allocate netlink skbs below the cut (allocation cut sites, A)
  skipCut allocCuts
  if ret == 0 then modify fun w => { w with routesViaWg0 := true }
  return ret

/-- W4: `wg_set_mtu`, `SIOCSIFMTU` on wg0 from the fixture's sender
    (`dev_ioctl` → `dev_set_mtu`): `-ENODEV` without wg0; the notifications
    of `NETDEV_CHANGEMTU` and the IPv6 and IPv4 teardowns below 1280 and 68
    allocate netlink skbs below the cut (allocation cut sites, A). The
    fixture's routes of a family taken down are gone until the next `wg_up`
    re-adds them; a transmit in between is outside the domain
    (`Syscalls.lean`). -/
def setMtu (mtu : Nat) : M Int := do
  if (← getK).wg.isNone then return -ENODEV
  let ret ← WG.setMtu mtu
  skipCut allocCuts
  return ret

/-- `wg_down`: `SIOCSIFFLAGS` without `IFF_UP`. `-ENODEV` without wg0; a
    down device does not change; an up one goes through `__dev_close_many`
    (`wg_stop`), and `NETDEV_DOWN` removes the routes. -/
def wgDown : M Int := do
  let some d := (← getK).wg | return -ENODEV
  if !d.running then return 0
  requireIdleDevice
  WG.wgDown
  -- `__dev_close_many`'s rtnetlink notifications and the routes' removal
  -- allocate netlink skbs below the cut (allocation cut sites, A)
  skipCut allocCuts
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
    | (_, bs) :: _ => bs.length
    | [] => -EAGAIN
  -- W5: each datagram with the TOS / traffic class the listener's cmsg
  -- reports (`IP_RECVTOS`, `IPV6_RECVTCLASS`): the outer DS field wg0 sent
  let datagrams := (w.listenerV4.map fun (ds, bs) => (4, ds, bs)) ++ (w.listenerV6.map fun (ds, bs) => (6, ds, bs))
  let entries := datagrams.map fun (f, ds, bs) =>
    Lean.toJson [Lean.toJson f, Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson ds, Lean.toJson (hex bs)]
  -- the sender's `recvmsg` source: a `sockaddr_in6` (SEND_FD is an IPv6
  -- socket), where an IPv4 source appears v4-mapped (::ffff:a.b.c.d), with
  -- its scope id (0: no kept source is link-local), then the TOS and the
  -- destination `IPV6_PKTINFO` reports (W5)
  let replies := w.senderInbox.map fun dg => let bs := dg.bytes
    let addr6 := if dg.family == AF_INET then 0xffff00000000 + dg.addr else dg.addr
    Lean.toJson [Lean.toJson AF_INET6, Lean.toJson (hex (beBytes addr6 16)), Lean.toJson dg.port, Lean.toJson (0 : Nat),
                 Lean.toJson dg.tos, Lean.toJson (hex (beBytes dg.dst 16)),
                 Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (if bs.length ≥ 12 then WG.u32le bs 8 else 0),
                 Lean.toJson (hex bs)]
  let sortJson (xs : List Lean.Json) := (xs.toArray.qsort fun a b => a.compress < b.compress).toList
  modify fun w => { w with listenerV4 := [], listenerV6 := [], senderInbox := [] }
  -- L: without wg0 the guest's RTM_GETLINK fails with ENODEV: `stats` null
  let stats := match (← getK).wg with
    | some d => Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped),
                                 ("rx_frame_errors", Lean.toJson d.rxFrameErrors),
                                 ("rx_length_errors", Lean.toJson d.rxLengthErrors),
                                 -- W5 (2.6): the device tstats; no transmit count in the driver
                                 ("rx_packets", Lean.toJson d.rxPackets), ("rx_bytes", Lean.toJson d.rxBytes),
                                 ("tx_packets", Lean.toJson d.txPackets), ("tx_bytes", Lean.toJson d.txBytes)]
    | none => Lean.Json.null
  return (ret, Lean.Json.mkObj [
    ("datagrams", Lean.Json.arr (sortJson entries).toArray),
    ("replies", Lean.Json.arr (sortJson replies).toArray),
    ("stats", stats)])

/-- The delivery of an inner packet that GRO flushed at `napi_complete_done`
    (a cut point): the receive-side stack model, `Leanux/Env/Stack.lean`
    (W5+W6), decides fail-closed what Linux does with it. -/
def deliverInner (pkt : List UInt8) : M Unit := Stack.receive pkt

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
    These placements differ only by the worker's state, which the poll does
    not read (the worker's remaining work is its next ring poll). A fourth,
    (c') inside `wg_queue_enqueue_per_peer_rx`, differs in the peer's
    reference count and is not told apart by the records (`napiIrqExit`).
    Without records (the domain filter) the poll runs at the first hook. -/
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

/-- (c') An interrupt at `__napi_schedule`'s `local_irq_restore`: its exit
    (`irq_exit_rcu` → `invoke_softirq`, `in_interrupt()` false in the
    worker) runs the NET_RX just raised **before** `wg_queue_enqueue_per_peer_rx`
    drops its peer reference (queueing.h:199-202). The records are those of
    (c) after the function (and of (b) at the next ring poll): a NET_RX
    section right after the enqueue. The poll's reads differ only in the
    peer's reference count, one higher here: its `kref_get_unless_zero` in
    the allowed-IPs lookup and its `wg_peer_put` compare it (KCOV operands;
    seen on a contended host, rx_roam_v6 and rx_in_order, 2026-10-06:
    Linux 1, 1, 3 where (c) gives 1, 1, 2). No record tells the two apart,
    so the placement is a choice the check enumerates
    (`World.napiBeforePut`): each choice is one complete execution, and
    the comparison child's operands must agree with one of them. Without
    records (the domain filter) the poll is placed by `napiSoftirq`. -/
def napiIrqExit : M Unit := do
  if (← get).hidden.isNone then return
  if !(← getDev).peers.toList.any (·.2.napiScheduled) then return
  if (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let w ← get
  let here := w.napiBeforePut.headD false
  set { w with napiBeforePut := w.napiBeforePut.drop 1, napiAmbiguous := w.napiAmbiguous + 1 }
  if here then napiSoftirq

/-- The decrypt worker (`packet_crypt_wq`, queued by `consume_data` in the
    injecting operation's NET_RX), once that softirq is done, with its
    NAPI softirq placements and its `cond_resched` (receive.c:505). -/
def runDecryptAt : Nat → M Unit
  | 0 => invariant "worker switches nested too deep"
  | fuel + 1 =>
    runWorker .decryptWorker (WG.decryptWorker napiSoftirq napiIrqExit (condResched fuel .decryptWorker (runDecryptAt fuel)))

def runDecryptWorker : M Unit := do
  runDecryptAt SWITCH_DEPTH
  if (← getDev).peers.toList.any (·.2.napiScheduled) then
    invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)"

/-- `wg_inject`: the fixture's sender sends one datagram to `port` on 127.0.0.1
    or ::1. Only wg0's own socket is in the domain: wg0 up, on that port.
    Loopback delivers it in softirq inside the `sendto`, and the guest waits
    for the handshake worker. -/
def inject (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) : M Int := do
  let some d := (← getK).wg | unsupported "a datagram to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a datagram to a port other than wg0's"
  -- a pending send worker inserts an index entry under a random index
  for pid in d.peerList do requireNotPending pid "receiving while a handshake is queued"
  fixtureSend
  let src ← senderSource family tos ll
  runWorker .netRx (WG.wgReceive msg src)
  -- the queued receive work runs before the guest's wait ends
  if !(← getDev).handshakeQueue.isEmpty then
    runWorker .receiveWorker (WG.handshakeReceiveWorker (discard <| condResched SWITCH_DEPTH .receiveWorker (runDecryptAt SWITCH_DEPTH)))
  -- or the decrypt worker, with the NAPI poll its packet schedules
  if !(← getDev).decryptQueue.isEmpty then runDecryptWorker
  -- then the crypt work the receive worker or the NAPI poll queued (a
  -- session's keepalive, staged packets on key confirmation)
  runCryptWorkers (runDecryptAt SWITCH_DEPTH)
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
               (HiddenSite.flowHashSecret).info.id, (HiddenSite.udpPortDraw).info.id,
               -- the first flood packet's `queue_work_on` of the receive work
               -- (dispatch order): its record sits in that packet's `net_rx`
               -- section; the mirror fills `handshakeQueue` below instead
               (HiddenSite.queued .receiveWorker).info.id]
  -- before the receive worker runs: the fixture's io_uring sends' producer
  -- `net_rx` sections and IP-layer cut draws
  let _ ← discardFloodRecords startW cuts
  -- the receive-worker section: the checked leading valid packets first, then
  -- the invalid flood discarded. The leading valids go through the real worker
  -- (which consumes the `cond_resched` records between packets); `floodDepth`
  -- keeps them over the under_load threshold.
  _ ← hidden (.sectionStart .receiveWorker)
  let src ← senderSource 4
  modifyDev fun d => { d with handshakeQueue := messages.map (fun m => (m, src)) }
  modify fun w => { w with floodDepth := count + messages.length }
  WG.handshakeReceiveWorker (discard <| condResched SWITCH_DEPTH .receiveWorker (runDecryptAt SWITCH_DEPTH))
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

/-! ## W7 stream B: `wg_batch` (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.5) -/

/-- A NAPI a receive scheduled inside this NET_RX section (consume_data's
    `-EPIPE` arm, W7 5.2): `net_rx_action`'s poll list runs it in the same
    pass, after the receive. -/
def pollScheduledInline : M Unit := do
  let d ← getDev
  let pending := d.peers.toList.filterMap fun (pid, p) => if p.napiScheduled then some pid else none
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  for pid in pending do
    discard <| WG.rxPoll pid WG.NAPI_POLL_WEIGHT fun pkts => pkts.forM deliverInner

/-- The deferred units a batch queued, run as the records order them: the
    decrypt worker, the crypt workers (the encrypt worker, then the tx
    workers by their dispatch records) and the handshake send workers,
    whichever section the next record starts. Work left when the records
    end outlived the guest's wait: outside the domain (its records would be
    missing). Without records (the domain filter) a fixed order. -/
def afterBatch : M Unit := do
  modify fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  if (← get).hidden.isNone then
    if !(← getDev).decryptQueue.isEmpty then runDecryptWorker
    runCryptWorkers (runDecryptAt SWITCH_DEPTH)
    runSendWorkers
    return
  for _ in [0:4096] do
    let d ← getDev
    let some site ← peekNextSite | break
    if site == startOf .decryptWorker && !d.decryptQueue.isEmpty then runDecryptWorker
    else if (site == startOf .encryptWorker && !d.encryptQueue.isEmpty)
         || (site == startOf .txWorker && !d.txWorkQueue.isEmpty) then runCryptWorkers (runDecryptAt SWITCH_DEPTH)
    else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorker
    else break
  let d ← getDev
  if !d.decryptQueue.isEmpty || !d.encryptQueue.isEmpty || !d.txWorkQueue.isEmpty || !d.sendWorkQueue.isEmpty then
    unsupported "work the batch queued outlived the guest's wait (its records would be missing)"
  deliverSent

/-- `wg_batch`: the fixture's sender submits `items` as one `io_uring_enter`,
    each an inject to wg0's port or a transmit into wg0, with no worker
    running between them (2.7: the sends run inline in the trace task, the
    kworkers wait for the call to return; a section between two items'
    records would mismatch). The completions present when the call returns
    are the operation's `cqes`: each item's length, or the sender's errno.
    Then the deferred units, by the records (`afterBatch`). The call returns
    the number of entries submitted. -/
def batch (items : List BatchItem) : M Int := do
  let some d := (← getK).wg | unsupported "a batch without wg0"
  if !d.running then unsupported "a batch with wg0 down"
  for pid in d.peerList do requireNotPending pid "a batch while a handshake is queued"
  let mut cqes : List Int := []
  for item in items do
    match item with
    | .inject family port msg =>
      if port != d.incomingPort then unsupported "a batch datagram to a port other than wg0's"
      fixtureSend
      let src ← senderSource family
      runWorker .netRx do
        WG.wgReceive msg src
        pollScheduledInline
      cqes := cqes ++ [(msg.length : Int)]
    | .xmit family addr payload opts =>
      if !(← get).routesViaWg0 then
        cqes := cqes ++ [-ENETUNREACH]
      else
        if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
          unsupported "a transmit after an MTU change took the family's routes into wg0 down"
        fixtureSend
        match ← xmitPackets family addr payload opts with
        | .error e => cqes := cqes ++ [e]
        | .ok (pkts, mtu) =>
          xmitMulticastLoop family addr
          let ret ← WG.wgXmit family addr pkts mtu
          cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  modify fun w => { w with extraOut := [("cqes", Lean.toJson cqes)] }
  afterBatch
  return items.length

end Leanux.Env
