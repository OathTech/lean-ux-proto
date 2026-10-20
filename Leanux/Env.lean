import Leanux.WG.Device
import Leanux.WG.Receive
import Leanux.WG.Data
import Leanux.WG.RxData
import Leanux.WG.Timers
import Leanux.Env.IpStack
import Leanux.Env.Batch
import Leanux.Env.Stack
import Leanux.Net.Route
import Leanux.Kernel.Signal
import Leanux.Seccomp.Prefill

/-!
# The environment model: the harness fixture and the WireGuard kworker

Not a mirror of C. This module holds what the trace's environment does, so
the mirror proper (`Leanux/WG`) contains only the C's data and control flow:
- the network fixture's listener port and the `wg_observe` operation, which
  waits, drains the fixture's listeners and reports wg0's counters;
- the fixture's bound ports (`portBound`) and its tables (W9: wg0's
  addresses and the default routes, `World.route4/6`), which `wg_up`,
  `wg_down`, `wg_delete`, `wg_deladdr` and `wg_delroute` change
  (docs/2026-10-05-l-lifecycle.md, section 5; docs/2026-10-06-w8-w9-netns-routing.md, 4.2);
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
(`Leanux/Env/Batch.lean`: `runWorker`, `sectionOf`, the NAPI poll's
placements, the activations and `schedule`). This file keeps the fixture,
the operations, the worker runners, the timers and the lifecycle: the hooks
the streams meet at.
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- The fixture's UDP listeners are on 127.0.0.1 and ::1 at this port. -/
def LISTEN_PORT : Nat := 51999

/-! ## epoll (docs/2026-10-12-epoll-design.md, sections 3.4, 3.5 and 5)

Fixture facts the epoll mirror depends on, none of them kernel state:
- the guest's fixture runs one `epoll_create1`, one ADD of a throwaway
  eventfd and two closes before the first trace of a boot (the warm-up,
  harness/guest.c `epoll_fixture`), so fs/eventpoll.c's boot-global
  `loop_check_gen` is at least 2 when a trace starts, a fresh set's `gen` of
  0 never equals it, and a set marked during one check holds an odd value no
  later even counter meets: the first-ADD arm of `do_epoll_ctl` (:2554) is
  dead in the domain. The mirror's counter is relative to the boot's unknown
  base; the three comparisons against it are operand exclusions;
- `max_user_watches`, computed at boot from the guest's memory, is read back
  by the fixture and checked by the harness (`EXPECTED_MAX_USER_WATCHES`,
  fail-closed) against the value here: an operand of every ADD;
- no task sleeps in `epoll_wait` (tier 1 waits with timeout 0), no signal
  is pending, `net.core.busy_poll` is 0, and the epoll paths touch no
  deferred unit. -/

/-- `loop_check_gen` at the start of every trace, relative (design 3.5). -/
def LOOP_CHECK_GEN_BASE : Nat := 2
/-- `/proc/sys/fs/epoll/max_user_watches` on the s5 oracle with the
    harness's fixed-size initramfs image (harness/linux.py `INITRAMFS_BYTES`,
    so the trace's size no longer moves it): `((totalram - totalhigh) / 25
    << PAGE_SHIFT) / EP_ITEM_COST` (fs/eventpoll.c:2814-2815), computed before
    the initramfs is freed. 53092 on W9 and e1 unpadded; re-measured at every
    oracle change, with harness/linux.py `EXPECTED_MAX_USER_WATCHES`. -/
def MAX_USER_WATCHES : Nat := 52958

/-- L (docs/2026-10-05-l-lifecycle.md, section 2.3): the ports where a
    wildcard UDP bind of wg0's conflicts with a fixture socket (no
    `SO_REUSEADDR`; a wildcard address matches any): the `127.0.0.1`
    listener's and the dual-stack `[::]` sender's. The `::1` listener is
    `v6only` at `LISTEN_PORT`, already excluded by the IPv4 bind. -/
def portBound (p : Nat) : Bool := p == LISTEN_PORT || p == SENDER_PORT

-- `LO_LINK_LOCAL` (W5, 2.5) is in Leanux/Kernel/Defs.lean, beside W9's tables.

/-- W1 (docs/2026-10-06-w1-w2-netlink.md, 2.1): the fixture namespace's
    devices besides wg0, for `lookup_interface`: `lo` (ifindex 1, no
    `rtnl_link_ops`, drivers/net/loopback.c) and `sit0` (ifindex 2, kind
    "sit": the per-netns fallback device of `CONFIG_IPV6_SIT=y`,
    net/ipv6/sit.c:1852-1860). wg0 is created third (ifindex 3; L's cursor
    gives 4 after a delete and re-create). -/
def fixtureNetDevices : List (String × Nat × Option String) := [("lo", 1, none), ("sit0", 2, some "sit")]

/-- Whether an endpoint is the fixture's sender: its port at a local address
    the wildcard bind (`[::]:51998`, dual-stack) receives at (W9,
    `World.wildcardLocal`: `127/8`, `::1`, wg0's addresses), or (W5) at the
    link-local address on `lo`. -/
def isSender (w : Net.Routing) (family addr port : Nat) : Bool :=
  port == SENDER_PORT && (w.wildcardLocal family addr || (family == AF_INET6 && addr == LO_LINK_LOCAL))

/-- What the sender's datagrams carry in their skb, by destination (W9,
    design section 2.5): the source is the route's `prefsrc` (`127.0.0.1`
    for `127/8`, the address itself for wg0's own), the destination the
    injected one, the loopback interface (ifindex 1); the DS field is the
    operation's `tos` (W5, 2.1: `IP_TOS` for a v4-mapped destination,
    `IPV6_TCLASS` otherwise, ECN bits kept); with `ll` (W5, 2.5) the source
    is the link-local address on `lo` (`IPV6_PKTINFO`), the destination
    `::1`. A datagram to wg0's address while it is not configured would
    route into wg0 instead: outside the domain. -/
def senderSource (family dest : Nat) (tos : Nat := 0) (ll : Bool := false) : M SkbSource := do
  let w ← getRouting
  if ll && dest != 0 then unsupported "a link-local source with a destination other than loopback"
  if family == 4 then
    if ll then unsupported "a link-local source for an IPv4 injection"
    match dest with
    | 0 => pure { family := 4, saddr := 0x7f000001, sport := SENDER_PORT, daddr := 0x7f000001, iif := 1, tos }
    | 1 =>
      if !w.addrs4.contains WG0_ADDR4 then unsupported "an injection to wg0's address while it is not configured"
      pure { family := 4, saddr := WG0_ADDR4, sport := SENDER_PORT, daddr := WG0_ADDR4, iif := 1, tos }
    | _ => pure { family := 4, saddr := 0x7f000001, sport := SENDER_PORT, daddr := 0x7f000002, iif := 1, tos }
  else if family == 6 then
    match dest with
    | 0 => pure { family := 6, saddr := if ll then LO_LINK_LOCAL else 1, sport := SENDER_PORT, daddr := 1, iif := 1, tos }
    | 1 =>
      if !w.addrs6.contains WG0_ADDR6 then unsupported "an injection to wg0's address while it is not configured"
      pure { family := 6, saddr := WG0_ADDR6, sport := SENDER_PORT, daddr := WG0_ADDR6, iif := 1, tos }
    | _ => unsupported "the loopback alias is IPv4 only"
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

/-- Deliver what wg0 sent (`World.sent`) over `lo` (W9: `send4`/`send6`
    already refused a route into wg0): to the fixture's sender (the
    wildcard bind, at any local address) or a listener, which keep the
    bytes for `wg_observe`; another local port has no socket, so the
    datagram is dropped there (the send itself succeeded). The sender's
    `recvfrom` reports the source `send4`/`send6` chose (`SentDatagram.src`:
    the cached or routed `fl.saddr`), no longer "the destination's own
    address" (design section 2.5). -/
def deliverSent : M Unit := do
  for dg in (← getWG).sent do
    let loopback := (dg.family == AF_INET && dg.addr / 2 ^ 24 == 127)
      || (dg.family == AF_INET6 && (dg.addr == 1 || dg.addr == LO_LINK_LOCAL))
    -- W1's hand-off of scoped IPv6 endpoints to W9 is superseded here: W5
    -- (2.5, `w5_scoped_*`) models the datagram to a link-local endpoint
    -- with its `sin6_scope_id` (the scoped outer source); W9's send6 owns
    -- the route lookup itself when it lands [AGENT, W integration].
    if isSender (← getRouting) dg.family dg.addr dg.port then
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
      modifyEnv fun w => { w with senderInbox := w.senderInbox ++ [src] }
    else match listenerFamily { family := dg.family, addr := dg.addr, port := dg.port } with
      | some 4 => modifyEnv fun w => { w with listenerV4 := w.listenerV4 ++ [(dg.ds, dg.bytes)] }
      | some _ => modifyEnv fun w => { w with listenerV6 := w.listenerV6 ++ [(dg.ds, dg.bytes)] }
      | none => if !loopback then unsupported "a datagram routed back into wg0"
  modifyWG fun w => { w with sent := [] }

/-- The crypt work a deferred unit queued, on the kernel's one CPU after
    that unit: the encrypt worker (`packet_crypt_wq`, queued by
    `wg_packet_create_data`) and the tx worker of each peer it queued
    (`wg_queue_enqueue_per_peer_tx`), as the records order them, with what
    they switched to (`schedule`). What they send is delivered. -/
def runCryptWorkers : M Unit := do
  schedule
  deliverSent

/-- After a wait's deferred units ran (`schedule`): work still queued
    outlived the guest's wait, outside the domain (its records would be
    missing). An activation suspended with an empty queue stays suspended:
    the records resume it at the scheduler's next turn (after a send worker
    or a timer section), and the operation ends with none (`Runner`). A NAPI
    poll still pending is a mirror defect: the decrypt worker's ring poll
    runs the softirq. -/
def requireDrained (what : String) (queues : List Bool) : M Unit := do
  if queues.any id then
    unsupported s!"work {what} outlived the guest's wait (its records would be missing)"
  -- a device-level unit still pending (`pendingDeviceUnits`) is a dispatch
  -- the kernel runs after the run that requeued it, with a section of its
  -- own (`Env.pendingDevice`); its absence from the records is the same
  -- domain exit as a queue left undrained (campaign 2's request 4,
  -- 2026-10-19: a constructed stream whose requeued encrypt unit never
  -- redispatched was accepted with its identity dangling)
  if let w :: _ ← pendingDeviceUnits then
    unsupported s!"{w.symbol} is pending at the end of the wait (the dispatch its requeue causes has no section in the records)"
  if (← getDev).peers.toList.any (·.2.napiScheduled) then
    invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)"

/-- Crypt work queued by a system call itself (a session's keepalive or
    staged packets sent from `wg_set` or `wg_up`): when the kworker runs it
    is not determined, since these operations' waits are not measured for
    it. `wg_xmit` has its own (`afterXmit`). -/
def requireNoCryptWork : M Unit := do
  let some d := (← getWG).dev | return
  if !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
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
  -- process_one_work clears PENDING as it takes the item; a second instance
  -- queued after that (its own entry in the queue) has set it again
  setPeer pid { p with handshakePending := (← getDev).sendWorkQueue.contains pid }
  runWorker .sendWorker (WG.handshakeSendWorker pid)

/-- The handshake send worker for each queued peer, oldest first, once the
    queuing system call has returned: the guest waits inside every operation
    that can queue it (`wg_set`, `wg_up`, `wg_xmit`), and the worker's remote
    KCOV section lands in that operation. -/
def runSendWorkers : M Unit := do
  if (← getWG).dev.isNone then return   -- L: no device, no worker
  requireNoCryptWork
  modifyWG fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  -- record-driven (review item 7): every turn runs a worker whose section
  -- consumes records; the queue may grow meanwhile (a response's initiation)
  for _ in [0:(← recordBudget)] do
    if (← getDev).sendWorkQueue.isEmpty then deliverSent; return
    runOneSendWorker
    schedule   -- a crypt activation the records resume after the section
  budgetExhausted "the send work queue"

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
  let some d := (← getWG).dev | return   -- L: no device (the send failed)
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    unsupported "wg_xmit queued crypt work and a handshake (their order)"
  modifyWG fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  if crypt then
    runCryptWorkers
    let d ← getDev
    requireDrained "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty]
  runSendWorkers

/-! ## D3: timers and the time advance (docs/2026-10-05-d3-timers.md, section 5.3)

Timer sections are accepted at the idle points, where the guest sleeps:
inside `wg_advance`'s wait and in the waits after `wg_set`, `wg_up`,
`wg_inject`, `wg_xmit` and before `wg_observe`. B3
(docs/2026-10-15-design-b3-timer-wheel.md, section 3.4): which timers fire,
and in what order, is the wheel's semantics (`Leanux/Kernel/TimerWheel.lean`),
checked against the sections in both directions (E1, `runTimers`;
`requireNothingDue`), with E2's lookahead telling a deferred softirq from a
timer that never fires. A timer section anywhere else is a hidden mismatch:
the mirror cannot run a callback mid-body. -/

/-- The site of the next record that is not ambient, without consuming
    anything (unlike `peekHiddenSite`). -/
def peekNextSite : M (Option Nat) := do
  let some rs := (← getAmbient).hidden | return none
  return (rs.find? fun r => !HiddenSite.passive r.site).map (·.site)

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
  modifyAmbient fun s => { s with fired := s.fired.push w.symbol }
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

/-- B3, E2's lookahead (docs/2026-10-15-design-b3-timer-wheel.md, section
    3.4): whether a section of callback `w` for the timer at `unit` (its
    address from the arm record; 0 when unknown) appears later in the trace's
    records: this operation's remainder, then the later operations
    (`World.hiddenAhead`). -/
def sectionAppearsLater (w : Worker) (unit : Nat) : M Bool := do
  let s ← get
  let startId := (HiddenSite.sectionStart w).info.id
  let names (r : HiddenRecord) : Bool :=
    r.site == startId && (unit == 0 || r.bytes.length < 16 || WG.recordWord r.bytes 1 == unit)
  return (s.ambient.hidden.getD []).any names || (s.fixture.hiddenAhead.getD []).any (·.any names)

/-- E1, item 3, at an end-of-wait read with pass bound `jPass`: no pending
    modeled timer's bucket is due. One that is, is either the timer softirq
    deferred past the read (its section appears later in the stream:
    `unsupported`, outside the fixture's timing domain, like the two-read gap
    above one tick) or a timer that never fires (a hidden mismatch: a bucket
    the mirror predicted, a deletion it missed, or a kernel that did not run
    it). E2. -/
def requireNothingDue (jPass : UInt64) : M Unit := do
  -- L: without wg0 (bare fixture, or after wg_delete) no WireGuard timer exists
  let some d := (← getWG).dev | return
  let some (pid, t, we) := TimerWheel.nextDue d jPass | return
  let w ← timerWorker t
  let unit := (((← getWG).timerUnits.find? fun e => e.2.1 == pid && e.2.2 == t).map (·.1)).getD 0
  if ← sectionAppearsLater w unit then
    unsupported s!"a due timer's softirq deferred past the end-of-wait read: peer {pid}'s {repr t} timer (bucket expiry {we.bucketExpiry}, the read {jPass}) fires later in the stream"
  throw (.hidden s!"a due timer did not fire: peer {pid}'s {repr t} timer, bucket expiry {we.bucketExpiry}, pending at the end-of-wait read {jPass}")

/-- E1, item 2: the records leave a step whose other pending timer is still
    due (the C runs a collected bucket to its end, `expire_timers`,
    timer.c:1813-1852): a hidden mismatch. -/
def requireStepComplete (b : UInt64) : M Unit := do
  if let some (pid, t) := TimerWheel.anotherAtStep (← getDev) b then
    throw (.hidden s!"a timer step split: peer {pid}'s {repr t} timer at bucket expiry {b} is still pending when the records leave the step")

/-- B3, E1 (docs/2026-10-15-design-b3-timer-wheel.md, section 3.4): the
    passes of an idle point whose pass bound is `jPass`, as the section
    stream places them, each constrained by the wheel:
    1. a timer section must be the earliest pending modeled bucket
       (`TimerWheel.nextDue`: ascending bucket expiry, the highest level
       first at one step, the newest enqueue first within a slot), due by
       `jPass`, and must name that timer (dispatch order); the timer is
       detached before the call (`expire_timers`, timer.c:1829) and the
       wheel is scanned afresh after the callback (a sibling the callback
       deleted does not run; one re-armed into its own slot keeps its bucket
       expiry and runs; one moved does not);
    2. a non-timer record may follow a step only when no other pending
       modeled timer sits at that step (a step is never split); the work
       between passes (the send and clear workers, the crypt workers, FIFO on
       their queues, ordered by their records) may arm or delete;
    3. at the read nothing is due (`requireNothingDue`, by the caller);
    4. no section runs a timer whose bucket is not due (item 1).
    A `T W N T` stream of two buckets due at different ticks of one wait is
    accepted; the environment's only freedom is where each pass's tick
    landed. Returns whether a timer fired. Work a timer queued that has not
    run when the records end outlived the guest's wait: outside the domain.
    Without records (the domain filter) nothing fires here. -/
def runTimers (jPass : UInt64) : M Bool := do
  modifyWG fun w => { w with queuedThisCall := [] }   -- the guest slept
  -- L: without wg0 (bare fixture, or after wg_delete) no WireGuard timer
  -- exists; a timer section in the records stays unconsumed and mismatches
  -- [AGENT, int-dl merge]
  if (← getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  -- record-driven (review item 7): every turn consumes a section or breaks
  for _ in [0:(← recordBudget)] do
    let some site ← peekNextSite | break
    let d ← getDev
    if let some w := timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          requireStepComplete b
          step := none
        if d.clearWorkQueue.isEmpty then break
        runOneClearWorker
      else
        let some (pid, t, we) := TimerWheel.nextDue d jPass
          | throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}")
        let expected ← timerWorker t
        if w != expected then
          throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
        -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
        -- section names, by the address its arm record carried
        if let some u ← peekUnit w then
          match (← getWG).timerUnits.find? (·.1 == u) with
          | some (_, pid', t') =>
            if pid' != pid || t' != t then
              throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
          | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
        if let some b := step then
          if b != we.bucketExpiry then requireStepComplete b
        delTimer pid t
        modifyWG fun s => { s with timerPassStep := some we.bucketExpiry }
        runTimerSection w (WG.timerCallback pid t)
        modifyWG fun s => { s with timerPassStep := none }
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        requireStepComplete b
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorker
      else
        -- the crypt work a timer queued, as the records order it, and a crypt
        -- activation the records resume after a section (`schedule`)
        runCryptWorkers
        if (← peekNextSite) == some site then break
  if let some b := step then requireStepComplete b
  if fired then
    deliverSent
    let d ← getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      unsupported "work a timer queued outlived the guest's wait"
  return fired

/-- The domain filter's stand-in for an idle point's passes (no records):
    every pending modeled timer whose bucket is due fires, in the wheel's
    order, then the crypt workers, the send workers and the clear work. A
    prediction for the filter's verdict only; the check follows the
    records. -/
def runTimersPlaceholder (jHi : UInt64) : M Unit := do
  modifyWG fun w => { w with queuedThisCall := [] }
  if (← getWG).dev.isNone then return   -- L: no wg0, no timers [AGENT, int-dl merge]
  -- the filter's own loop (review item 7): one turn per pending timer at most
  let pending := (← getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let some (pid, t, _) := TimerWheel.nextDue (← getDev) jHi | break
    delTimer pid t
    runTimerSection (← timerWorker t) (WG.timerCallback pid t)
  runCryptWorkers
  runSendWorkers
  for _ in [0:(← getDev).clearWorkQueue.length + 1] do
    if (← getDev).clearWorkQueue.isEmpty then break
    runOneClearWorker

/-- An idle point (the guest's waits after `wg_set`, `wg_up`, `wg_inject`,
    `wg_xmit` and `wg_batch`, and before `wg_observe`), where a timer may
    fire naturally. Review item 7: the guest reads `jiffies` at the end of
    the wait (kind 310, `HiddenSite.jiffiesEnd`, in the remote stream after
    the wait's sections), read ahead of the sections it bounds and consumed
    after them. B3: the read is the pass bound `J_pass` of E1 (a tick
    between the last pass and the read would have run another pass before
    the task resumed, `__irq_exit_rcu`, softirq.c:661-662, but for E2's
    deferral), so every modeled bucket due by it has fired, in the wheel's
    order, and none beyond it has. No record of the read in the operation
    is a hidden mismatch (a capture without the instrument). Without records
    (the domain filter) the filter's prediction uses `Timing`'s constants. -/
def idleTimers : M Unit := do
  let w ← getWG
  let a ← getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholder jHi else discard <| runTimers jHi
    return
  let some jEnd ← peekSiteU64 .jiffiesEnd
    | throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation")
  discard <| runTimers jEnd
  requireNothingDue jEnd
  let j ← hiddenJiffies .jiffiesEnd
  if j != jEnd then invariant "the end-of-wait jiffies record changed between the peek and the read"
  modifyWG fun w => { w with jiffiesLast := some j }

/-- `wg_advance`'s ioctl: `leanux_time_advance` moves `jiffies_64` by
    `ticks` (`do_timer`), and the ioctl records kind 304 `{before, after}`
    (`.timeAdvance`) and returns 0. The record must show exactly `ticks`;
    `after` becomes the last known `jiffies`. The window rule needs every
    pending timer's recorded expiry, so with records but without arm records
    an advance is outside the domain. Without records (the domain filter)
    the advance starts from the last known `jiffies` (0 before any). -/
def advance (ticks : Nat) : M Int := do
  let w ← getWG
  let a ← getAmbient
  let (j0, j1) ← if a.hidden.isNone && a.hiddenPlaceholders then
      let j0 := w.jiffiesLast.getD 0
      pure (j0, j0 + ticks.toUInt64)
    else do
      if !a.armRecords then unsupported "a time advance without arm records (the timers' expiries are unknown)"
      let bs ← hidden .timeAdvance
      pure (WG.recordWord64 bs 0, WG.recordWord64 bs 1)
  -- `jiffies_64 += ticks` on `unsigned long` (review item 8): the difference
  -- is exact modulo 2^64, as the kernel's
  if j1 - j0 != ticks.toUInt64 then
    throw (.hidden s!"the advance moved jiffies from {j0} to {j1}, not by {ticks}")
  modifyWG fun w => { w with jiffiesLast := some j1 }
  modifyEnv fun e => { e with lastAdvance := some (j0, j1) }
  return 0

/-- The guest's wait after `wg_advance`'s ioctl (stream K, section 13.3: until
    the monotonic clock has absorbed the advance, then `ADVANCE_WAIT_US`):
    the next tick raises `TIMER_SOFTIRQ`, the due callbacks run in sections,
    then the work they queue, all in this operation's records. B3 (E1): the
    jump itself raises nothing (`leanux_time_advance` moves `jiffies_64` with
    interrupts off; the softirq is raised by the next real tick,
    timer.c:2502-2504), so a pass over what the jump made due has run only if
    a tick followed it, which the read shows as `J_end > after`; with
    `J_end = after` the pass bound is `before` and the sections land in the
    next operation (the timer control `tc_advance_wait0`). -/
def afterAdvance : M Unit := do
  let w ← getWG
  let a ← getAmbient
  if a.hidden.isNone then
    -- the domain filter's prediction (no records): the fixture's wait
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then runTimersPlaceholder jHi else discard <| runTimers jHi
    return
  -- review item 7: the window ends at the recorded end of the advance's wait
  let some jEnd ← peekSiteU64 .jiffiesEnd
    | throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance")
  let some (j0, j1) := (← getEnv).lastAdvance | invariant "afterAdvance without an advance"
  let jPass := if timeAfter jEnd j1 then jEnd else j0
  discard <| runTimers jPass
  requireNothingDue jPass
  let j ← hiddenJiffies .jiffiesEnd
  if j != jEnd then invariant "the end-of-wait jiffies record changed between the peek and the read"
  modifyWG fun w => { w with jiffiesLast := some j }

/-- Work a down or a deletion would leave behind: crypt work (its worker's
    timing) and a decrypt queue or NAPI poll still pending
    (docs/2026-10-05-l-lifecycle.md, section 9). -/
def requireIdleDevice : M Unit := do
  requireNoCryptWork
  let d ← getDev
  if !d.decryptQueue.empty || d.peers.toList.any (·.2.napiScheduled) then
    unsupported "receive work queued at wg_stop (its worker's timing)"

/-- `wg_up`: `SIOCSIFFLAGS` with `IFF_UP` (`dev_ifsioc`, `dev_change_flags`).
    Without wg0, `-ENODEV` (`dev_load` requests no module: no
    `CONFIG_MODULES`). An up device does not change (`__dev_change_flags`
    sees no `IFF_UP` change, dev.c:8962). Otherwise the mirror's `wgUp`;
    after a success the guest adds wg0's addresses and routes. -/
def wgUp : M Int := do
  let some d := (← getWG).dev | return -ENODEV
  if d.running then return 0
  let ret ← WG.wgUp
  -- `dev_change_flags`' rtnetlink notifications and the fixture's routes
  -- allocate netlink skbs below the cut (allocation cut sites, A)
  skipCut allocCuts
  if ret == 0 then
    -- lane C: `__dev_open`'s `NETDEV_UP` notifiers, devinet's first
    -- (`ip_mc_up` joins all-hosts: `ip_rt_multicast_event` flushes,
    -- igmp.c:1484-1486), then `fib_netdev_event` (fib_frontend.c:1491-1500:
    -- the surviving address's routes added again after a down, the
    -- generation and a flush)
    Net.Fib.rtCacheFlush
    Net.Fib.netdevUp WG0_IFINDEX
  -- W9: the guest's `route_into_wg0` adds wg0's addresses and default routes
  -- after this operation's wait (design 14.3b): `routeIntoWg0` applies them
  -- once the send workers and the idle timers have run
  if ret == 0 then modifyEnv fun w => { w with routesPending := true }
  return ret

/-- `inetdev_destroy(in_dev)` (devinet.c:313-336) for wg0: `in_dev->dead`,
    then each address deleted through the inetaddr chain (`NETDEV_DOWN`,
    `fib_del_ifaddr` with the scan skipped), the last one disabling IP on
    the device (`fib_inetaddr_event`, fib_frontend.c:1459-1471). -/
def inetdevDestroy : M Unit := do
  let w ← getRouting
  let addrs := w.addrs4
  modifyRouting fun w => { w with addrs4 := [], addrPlens4 := [] }
  let mut rest := addrs
  for a in addrs do
    rest := rest.drop 1
    Net.Fib.inetaddrDown WG0_IFINDEX a ((w.addrPlens4.lookup a).getD 32) rest.isEmpty true

/-- W4: `wg_set_mtu`, `SIOCSIFMTU` on wg0 from the fixture's sender
    (`dev_ioctl` → `dev_set_mtu`): `-ENODEV` without wg0; the notifications
    of `NETDEV_CHANGEMTU` and the IPv6 and IPv4 teardowns below 1280 and 68
    allocate netlink skbs below the cut (allocation cut sites, A). The
    fixture's routes of a family taken down are gone until the next `wg_up`
    re-adds them; a transmit in between is outside the domain
    (`Syscalls.lean`). -/
def setMtu (mtu : Nat) : M Int := do
  if (← getWG).dev.isNone then return -ENODEV
  let old := (← getDev).mtu
  -- the guest fills `ifr_mtu` with `(int)op->a` (guest.c): the trace's u32
  -- word reaches `dev_set_mtu` negative at or above 2^31
  let newMtu : Int := if mtu ≥ 2 ^ 31 then (mtu : Int) - 2 ^ 32 else mtu
  -- lane C: an MTU raised back over IPV4_MIN_MTU re-creates the in_device
  -- (`inetdev_event` `NETDEV_CHANGEMTU` → `inetdev_init`, devinet.c:1620-1626),
  -- a path the mirror does not model: the fixture's addresses stay gone
  -- until the next up on this fixture only when the MTU stays below 68
  if old < 68 && newMtu ≥ 68 then unsupported "an MTU raised back over IPV4_MIN_MTU (inetdev_init re-creates the in_device)"
  let ret ← WG.setMtu newMtu
  skipCut allocCuts
  -- W9's tables (docs/2026-10-06-w8-w9-netns-routing.md, 14.3d): the
  -- NETDEV_CHANGEMTU notifiers, which `dev_set_mtu_ext` calls only for a
  -- changed MTU (dev.c:9090-9091 returns 0 before them for the same one).
  -- fib_netdev_event runs fib_sync_mtu and rt_cache_flush on every change
  -- (fib_frontend.c:1519-1522), so every cached IPv4 dst expires; below
  -- IPV4_MIN_MTU (68) inetdev_event destroys the in_device
  -- (devinet.c:1637-1643): the IPv4 address goes and with it the routes via
  -- wg0 (fib_del_ifaddr, fib_disable_ip); below IPV6_MIN_MTU (1280)
  -- addrconf_ifdown removes the IPv6 addresses and routes
  -- (addrconf.c:3691-3695) and moves the sernum. A later wg_up re-adds
  -- them (routeIntoWg0).
  if ret == 0 && mtu != old then
    -- lane C: `NETDEV_CHANGEMTU`'s notifiers in order: devinet's
    -- `inetdev_event` destroys the `in_device` below 68 (devinet.c:1637-1643:
    -- each address deleted through the inetaddr chain, the last disabling
    -- IP on the device), then `fib_netdev_event` (`fib_sync_mtu`, a flush,
    -- fib_frontend.c:1519-1522) and nexthop.c's flush (:3884-3887)
    if mtu < 68 then inetdevDestroy
    Net.Fib.netdevChangeMtu
    modifyRouting fun w => { w with addrs6 := if mtu < 1280 then [] else w.addrs6,
                                    defaultRoute6 := mtu ≥ 1280 && w.defaultRoute6,
                                    ipv6Gen := if mtu < 1280 then w.ipv6Gen + 1 else w.ipv6Gen }
  return ret

/-- A fixture request the guest issues after the operation's coverage
    capture (`harness/guest.c`: `route_into_wg0` follows the capture at the
    syscall's return): its choice points are outside the window, so the steps
    it records are discarded, as the boot's are (`Runner`). Its state
    changes, its environment calls and a stop stand. -/
def outsideWindow (m : M α) : M α := do
  let steps := (← getAmbient).steps
  let r ← m
  modifyAmbient fun w => { w with steps }
  return r

/-- W9 (design 14.3b): `route_into_wg0` after a successful flag-changing
    `wg_up`, once the operation's wait is over: wg0's addresses (the IPv4
    one may survive a down) and the default routes; every table change
    bumps a generation (`rt_cache_flush`; the IPv6 sernum), which expires a
    dst the handshake worker cached during the wait. The fixture puts the
    wait before the adds so this order is the only one. -/
def routeIntoWg0 : M Unit := do
  if !(← getEnv).routesPending then return
  let addrAlready := (← getRouting).addrs4.contains WG0_ADDR4
  -- lane C: the IPv4 requests on the trie (`Net.Fib.routeIntoWg0`): the
  -- address through the inetaddr chain, the default route and the W4
  -- routes through `fib_table_insert`, each a `rt_cache_flush`. The guest
  -- issues them after the operation's coverage capture (the design note,
  -- 9.1), so their choice points are outside the window
  -- W4: below IPV4_MIN_MTU the in_device is gone (`setMtu`), and the guest's
  -- address add is refused (-ENOBUFS, devinet.c:888), its route adds with it
  -- (-ENODEV): nothing enters the tables until a later MTU change and up
  let down4 := (← getDev).mtu < 68
  modifyEnv fun w => { w with routesPending := false }
  if !down4 then
    modifyRouting fun w => { w with addrs4 := if addrAlready then w.addrs4 else w.addrs4 ++ [WG0_ADDR4] }
    let routes4 := (← getEnv).routes.filterMap fun (f, a, m) => if f == 4 then some (a, m) else none
    outsideWindow (Net.Fib.routeIntoWg0 addrAlready WG0_ADDR4 routes4)
  modifyRouting fun w => { w with addrs6 := [WG0_ADDR6], defaultRoute6 := true, ipv6Gen := w.ipv6Gen + 1 }

/-- `wg_down`: `SIOCSIFFLAGS` without `IFF_UP`. `-ENODEV` without wg0; a
    down device does not change; an up one goes through `__dev_close_many`
    (`wg_stop`), and `NETDEV_DOWN` removes the routes. -/
def wgDown : M Int := do
  let some d := (← getWG).dev | return -ENODEV
  if !d.running then return 0
  requireIdleDevice
  WG.wgDown
  -- `__dev_close_many`'s rtnetlink notifications and the routes' removal
  -- allocate netlink skbs below the cut (allocation cut sites, A)
  skipCut allocCuts
  -- lane C: `NETDEV_DOWN`'s notifiers in order: devinet's `ip_mc_down` (a
  -- flush), then `fib_netdev_event` → `fib_disable_ip(dev, NETDEV_DOWN,
  -- false)` (fib_frontend.c:1501-1503): the routes via wg0 whose nexthop
  -- scope is not `RT_SCOPE_NOWHERE` go dead and are flushed; the local
  -- route of the surviving address stays. W9: the IPv6 address and routes
  -- go (`keep_addr_on_down` 0)
  Net.Fib.rtCacheFlush
  Net.Fib.netdevDown WG0_IFINDEX
  modifyRouting fun w => { w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen + 1 }
  return 0

/-- `wg_delete`: `RTM_DELLINK` (the mirror's `wgDelete`); `NETDEV_DOWN` and
    `NETDEV_UNREGISTER` remove every route via wg0. -/
def wgDelete : M Int := do
  if (← getWG).dev.isSome then requireIdleDevice
  -- Pre-release review finding 6 (docs/2026-10-14-pre-release-review.md,
  -- section 6; W2 design 5): the guest refuses `wg_delete` while a stepped
  -- dump is pending (`guest.c` `wg_delete_with_dump_pending`: the dump's
  -- cursor holds the device reference, W2 C1), and the mirror's cursor does
  -- not carry that reference, so the composition is outside the domain here
  -- too, fail-closed, rather than a delete the guest would never perform.
  -- pending as the guest counts it: started, and its NLMSG_DONE not yet
  -- received (`dump_pending`, guest.c), which outlasts `cb_running` by the
  -- queued chunks
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← getWG
  if pending k.nlSock7 || pending k.nlSock8 then
    unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)"
  -- lane C: `dev_close_many`'s `NETDEV_DOWN` (as `wgDown`'s) and
  -- `NETDEV_UNREGISTER`'s notifiers in order: devinet's `inetdev_destroy`
  -- deletes each address through the inetaddr chain (the last disabling IP
  -- on the device), then `fib_disable_ip(dev, NETDEV_UNREGISTER, true)`
  -- (fib_frontend.c:1487-1490); W9: the IPv6 address and routes go too
  let onDown : M Unit := do
    Net.Fib.rtCacheFlush
    Net.Fib.netdevDown WG0_IFINDEX
    modifyRouting fun w => { w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen + 1 }
  let onUnregister : M Unit := do
    inetdevDestroy
    Net.Fib.netdevUnregister WG0_IFINDEX
    modifyRouting fun w => { w with addrs6 := [], defaultRoute6 := false, ipv6Gen := w.ipv6Gen + 1 }
  let ret ← WG.wgDelete onDown onUnregister
  return ret

/-- W9 `wg_deladdr` (design section 4.3): `RTM_DELADDR` of wg0's fixture
    address; `-EADDRNOTAVAIL` when it is absent. IPv4: the device's only
    address goes, so `fib_inetaddr_event` NETDEV_DOWN disables the device's
    routes as well (`fib_disable_ip`, `fib_frontend.c:1461-1469`): the
    default route via wg0 is gone and `rt_genid` moves. IPv6: the address
    and its local route go, the default route stays, the sernum moves. -/
def wgDeladdr (family : Nat) : M Int := do
  if (← getWG).dev.isNone then unsupported "wg_deladdr without wg0 (the request names a stale ifindex)"
  let w ← getRouting
  if family == 4 then
    -- the request names the fixture's address (`deladdr_wg0`)
    if !w.addrs4.contains WG0_ADDR4 then return -EADDRNOTAVAIL
    -- lane C: `__inet_del_ifa` unlinks the address, then the inetaddr
    -- chain's `NETDEV_DOWN`: `fib_del_ifaddr`, the generation, and the
    -- last address disabling IP on the device (fib_frontend.c:1459-1471)
    let rest := w.addrs4.filter (· != WG0_ADDR4)
    modifyRouting fun _ => { w with addrs4 := rest }
    Net.Fib.inetaddrDown WG0_IFINDEX WG0_ADDR4 32 rest.isEmpty false
  else
    if w.addrs6.isEmpty then return -EADDRNOTAVAIL
    modifyRouting fun _ => { w with addrs6 := [], ipv6Gen := w.ipv6Gen + 1 }
  return 0

/-- W9 `wg_delroute`: `RTM_DELROUTE` of the default route via wg0; `-ESRCH`
    when absent. IPv4's `rt_genid` moves only if the route was ever looked
    up (`fib_table_delete`, `fib_trie.c:1754-1755`, `FA_S_ACCESSED`); the
    IPv6 sernum moves unconditionally (`fib6_del`). -/
def wgDelroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) : M Int := do
  if (← getWG).dev.isNone then unsupported "wg_delroute without wg0 (the request names a stale ifindex)"
  let w ← getRouting
  if family == 4 then
    -- lane C: `inet_rtm_delroute` → `fib_table_delete` on the trie with the
    -- guest's request (`delroute_wg0`): `-ESRCH` when absent, the flush only
    -- if the alias was accessed (fib_trie.c:1754-1755). A named route
    -- (`delroute_request`): table main, any protocol and scope, the type
    -- when given, the device and metric when given
    if named then
      let type := (Net.Fib.RouteType.ofCode? typeCode).getD .unspec
      return ← Net.Fib.tableDelete { dst, dstLen := plen, table := Net.Fib.RT_TABLE_MAIN, protocol := 0,
                                     scope := Net.Fib.RT_SCOPE_NOWHERE, type, oif, priority := metric }
    return ← Net.Fib.delrouteWg0
  else
    if !w.defaultRoute6 then return -ESRCH
    modifyRouting fun _ => { w with defaultRoute6 := false, ipv6Gen := w.ipv6Gen + 1 }
  return 0

/-- Lane C `wg_addroute`: `RTM_NEWROUTE` over L's temporary rtnetlink socket
    (`inet_rtm_newroute` → `rtm_to_fib_config` → `fib_new_table` →
    `fib_table_insert`, fib_frontend.c:899-926): table main, protocol
    static, scope link for a unicast route via `oif` and universe for a
    reject type, the metric and `RTAX_MTU` when given, `NLM_F_CREATE` and
    the trace's flags. A stale ifindex (no wg0) fails in `fib_create_info`
    (`-ENODEV`). The result is the acknowledgement's error. -/
def wgAddroute (dst plen oif typeCode metric mtu nlflags : Nat) : M Int := do
  let some type := Net.Fib.RouteType.ofCode? typeCode | invariant "wg_addroute: an unknown route type"
  let cfg : Net.Fib.Config :=
    { dst, dstLen := plen, table := Net.Fib.RT_TABLE_MAIN, protocol := Net.Fib.RTPROT_STATIC,
      scope := if type == .unicast then Net.Fib.RT_SCOPE_LINK else Net.Fib.RT_SCOPE_UNIVERSE,
      type, oif, priority := metric, mtu, nlflags := Net.Fib.NLM_F_CREATE ||| nlflags }
  Net.Fib.tableInsert cfg

/-- Lane C `wg_addaddr`: `RTM_NEWADDR` of another IPv4 address on wg0
    (`inet_rtm_newaddr`, devinet.c:966-1030, `NLM_F_CREATE | NLM_F_EXCL`):
    `-ENODEV` for a stale ifindex, `-ENOBUFS` without the `in_device`
    (:888), `-EEXIST` for an address already there with its prefix
    (`find_matching_ifa`); a secondary (an address in the prefix of one
    already there, `__inet_insert_ifa` :530-541) and another primary with
    the same local are not modelled. Then `__inet_insert_ifa`'s
    `NETDEV_UP` through the inetaddr chain (`fib_add_ifaddr`: the local
    route, the prefix route and its broadcast). -/
def wgAddaddr (addr plen : Nat) : M Int := do
  let some d := (← getWG).dev | return -ENODEV
  if !d.inet4Dev then return -ENOBUFS
  let w ← getRouting
  let mask := if plen == 0 then 0 else Net.Fib.KEY_MAX - (2 ^ (32 - plen) - 1)
  for a in w.addrs4 do
    let p := (w.addrPlens4.lookup a).getD 32
    if a == addr && p == plen then return -EEXIST
    if a == addr then unsupported "wg_addaddr of an address already there with another prefix (a second primary)"
    if p == plen && a &&& mask == addr &&& mask then unsupported "wg_addaddr of a secondary address (in the prefix of one already there)"
  modifyRouting fun w => { w with addrs4 := w.addrs4 ++ [addr], addrPlens4 := w.addrPlens4 ++ [(addr, plen)] }
  Net.Fib.inetaddrUp WG0_IFINDEX addr plen
  return 0

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
  if let some d := (← getWG).dev then
    if !d.sendWorkQueue.isEmpty then unsupported "send work queued by an operation that does not wait"
  requireNoCryptWork
  deliverSent
  let w ← getEnv
  let foreignCreator := (← getRouting).foreignCreator
  let hex (bs : List UInt8) : String := String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])
  -- the guest reports type 0 for a datagram shorter than 4 bytes
  let type (bs : List UInt8) : Nat := if bs.length ≥ 4 then WG.u32le bs 0 else 0
  -- W8: after wg_netns_close the listeners are closed: `recvfrom(4)` is
  -- -EBADF and the datagrams are null (the guest prints null)
  let closed := foreignCreator && w.netnsCHolders.isEmpty
  let ret : Int := if closed then -EBADF else match w.listenerV4 with
    | (_, bs) :: _ => bs.length
    | [] => -EAGAIN
  -- W5: each datagram with the TOS / traffic class the listener's cmsg
  -- reports (`IP_RECVTOS`, `IPV6_RECVTCLASS`): the outer DS field wg0 sent
  -- Ordered as the harness orders Linux's (harness/linux.py attach_observed):
  -- a stable sort by peer key (the listener's family and the message's index
  -- word at byte 4), keeping arrival order within a peer's session and
  -- leaving the cross-peer interleaving free (pre-release review, finding 5)
  let indexWord (bs : List UInt8) : Nat := if bs.length ≥ 8 then WG.u32le bs 4 else 0
  let keyLt (a b : Nat × Nat × Nat) : Bool :=
    a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
  let stableSortBy {α : Type} (key : α → Nat × Nat × Nat) (xs : List α) : List α :=
    ((((List.range xs.length).zip xs).toArray.qsort fun (i, a) (j, b) => keyLt (key a) (key b) || (key a == key b && i < j)).map (·.2)).toList
  let datagrams := stableSortBy (fun (f, _, bs) => (f, indexWord bs, 0))
    ((w.listenerV4.map fun (ds, bs) => (4, ds, bs)) ++ (w.listenerV6.map fun (ds, bs) => (6, ds, bs)))
  let entries := datagrams.map fun (f, ds, bs) =>
    Lean.toJson [Lean.toJson f, Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson ds, Lean.toJson (hex bs)]
  -- the sender's `recvmsg` source: a `sockaddr_in6` (SEND_FD is an IPv6
  -- socket), where an IPv4 source appears v4-mapped (::ffff:a.b.c.d), with
  -- its scope id (0: no kept source is link-local), then the TOS and the
  -- destination `IPV6_PKTINFO` reports (W5)
  let inbox := stableSortBy
    (fun dg => ((if dg.family == AF_INET then 0xffff00000000 + dg.addr else dg.addr), dg.port, indexWord dg.bytes))
    w.senderInbox
  let replies := inbox.map fun dg => let bs := dg.bytes
    let addr6 := if dg.family == AF_INET then 0xffff00000000 + dg.addr else dg.addr
    Lean.toJson [Lean.toJson AF_INET6, Lean.toJson (hex (beBytes addr6 16)), Lean.toJson dg.port, Lean.toJson (0 : Nat),
                 Lean.toJson dg.tos, Lean.toJson (hex (beBytes dg.dst 16)),
                 Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (if bs.length ≥ 12 then WG.u32le bs 8 else 0),
                 Lean.toJson (hex bs)]
  modifyEnv fun w => { w with listenerV4 := [], listenerV6 := [], senderInbox := [] }
  -- L: without wg0 the guest's RTM_GETLINK fails with ENODEV: `stats` null
  let stats := match (← getWG).dev with
    | some d => Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped),
                                 ("rx_frame_errors", Lean.toJson d.rxFrameErrors),
                                 ("rx_length_errors", Lean.toJson d.rxLengthErrors),
                                 -- W5 (2.6): the device tstats; no transmit count in the driver
                                 ("rx_packets", Lean.toJson d.rxPackets), ("rx_bytes", Lean.toJson d.rxBytes),
                                 ("tx_packets", Lean.toJson d.txPackets), ("tx_bytes", Lean.toJson d.txBytes)]
    | none => Lean.Json.null
  return (ret, Lean.Json.mkObj [
    ("datagrams", if closed then Lean.Json.null else Lean.Json.arr entries.toArray),
    ("replies", Lean.Json.arr replies.toArray),
    ("stats", stats)])

/-- `wg_inject`: the fixture's sender sends one datagram to `port` on 127.0.0.1
    or ::1. Only wg0's own socket is in the domain: wg0 up, on that port.
    Loopback delivers it in softirq inside the `sendto`, and the guest waits
    for the handshake worker. -/
def inject (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) (dest : Nat := 0) : M Int := do
  -- W8 (design 3.1, 3.4): in the foreign-creator fixture the injector lives
  -- in the creating namespace: gone after wg_netns_close, and wg0's own
  -- address (in the device namespace) is unroutable from it
  if (← getRouting).foreignCreator then
    if (← getEnv).netnsCHolders.isEmpty then unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)"
    if dest == 1 then unsupported "wg_inject to wg0's address from the creating namespace (unroutable)"
  let some d := (← getWG).dev | unsupported "a datagram to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a datagram to a port other than wg0's"
  -- a pending send worker inserts an index entry under a random index
  for pid in d.peerList do requireNotPending pid "receiving while a handshake is queued"
  fixtureSend
  let src ← senderSource family dest tos ll
  -- lane C: the injector's `udp_sendmsg` routes the datagram in its own
  -- namespace (`ip_route_output_flow`, a wildcard source): a local route
  -- whose source is the one `senderSource` states; the loopback output
  -- creates lo's one neighbour
  if family == 4 then
    match ← Net.Fib.inSocketNs (Net.routeOutput4 0 src.daddr) with
    | .error _ => invariant "wg_inject: the injector's datagram has no route"
    | .ok r =>
      if r.dev != LO_IFINDEX || r.src != src.saddr then invariant "wg_inject: the route disagrees with the sender source"
      Net.Fib.inSocketNs (Net.neighbourClassify LO_IFINDEX)
  runWorker .netRx (WG.wgReceive msg src)
  -- the queued work runs before the guest's wait ends: the receive worker,
  -- the decrypt worker with the NAPI poll its packet schedules, and the
  -- crypt work they queue (a session's keepalive, staged packets on key
  -- confirmation), as the records order them
  runCryptWorkers
  let d ← getDev
  requireDrained "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty]
  return msg.length   -- udp_sendmsg returns the datagram's length

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
  modifyWG fun w => { w with queuedThisCall := [] }   -- the call returned and slept
  if (← getAmbient).hidden.isNone then
    runCryptWorkers
    runSendWorkers
    return
  -- record-driven (review item 7): every turn runs a unit whose section consumes records
  for _ in [0:(← recordBudget)] do
    schedule
    if (← peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← getDev).sendWorkQueue.isEmpty then
      runOneSendWorker
    else break
  let d ← getDev
  -- the completion guard: every queue a dispatched unit drains, as the
  -- injection path's (`inject`), and every device-level unit's PENDING bit
  -- (`requireDrained`). The handshake receive queue and its counter were
  -- omitted until 2026-10-15 (campaign 2's request 1: a constructed stream
  -- that queues the receive worker and never dispatches it was accepted).
  -- The pending bits were left unchecked then on the premise that a pending
  -- unit always has a non-empty queue in the mirror's transitions; campaign
  -- 2's request 4 (2026-10-19) refuted it with a requeue during the unit's
  -- own run, whose redispatch the kernel runs with an empty ring.
  requireDrained "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
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
  let some d := (← getWG).dev | unsupported "a batch without wg0"
  if !d.running then unsupported "a batch with wg0 down"
  for pid in d.peerList do requireNotPending pid "a batch while a handshake is queued"
  let mut cqes : List Int := []
  for item in items do
    match item with
    | .inject family port msg =>
      if port != d.incomingPort then unsupported "a batch datagram to a port other than wg0's"
      fixtureSend
      let src ← senderSource family 0
      -- lane C: the sender's route to loopback and lo's one neighbour
      if family == 4 then
        match ← Net.routeOutput4 0 src.daddr with
        | .error _ => invariant "wg_batch: the datagram to wg0's port has no route"
        | .ok r =>
          if r.dev != LO_IFINDEX || r.src != src.saddr then invariant "wg_batch: the route disagrees with the sender source"
          Net.neighbourClassify LO_IFINDEX
      runWorker .netRx do
        WG.wgReceive msg src
        pollScheduledInline
      cqes := cqes ++ [(msg.length : Int)]
    | .xmit family addr payload opts =>
      -- W9: the sender's `sendto` routes on the fixture's tables; a local
      -- destination never reaches wg0
      match ← Net.routeLookup family 0 addr with
      | .error err => cqes := cqes ++ [err]
      | .ok r =>
        if r.dev != WG0_IFINDEX then unsupported "a batch transmit to a local address (not into wg0)"
        if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
          unsupported "a transmit after an MTU change took the family's routes into wg0 down"
        fixtureSend
        -- lane C: `dst_mtu` is the route's metric when it carries one
        let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
        match ← xmitPackets family addr payload opts with
        | .error e => cqes := cqes ++ [e]
        | .ok (pkts, mtu) =>
          xmitMulticastLoop family addr
          -- lane C: `ip_finish_output2` on wg0: the device's one neighbour
          if family == 4 then Net.neighbourClassify WG0_IFINDEX
          let ret ← WG.wgXmit family addr pkts mtu
          cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  modifyAmbient fun w => { w with extraOut := [("cqes", Lean.toJson cqes)] }
  afterBatch
  return items.length

/-! ## E-B over W7: `wg_flood` as a batch (B4, docs/2026-10-15-design-b4-load-ratelimiter.md 2.3) -/

/-- `wg_flood` (docs/2026-10-05-e-dos.md §8; B4, docs/2026-10-15-design-b4-load-ratelimiter.md
    2.3): the fixture submits one `io_uring_enter` of sends to wg0's port
    (harness/guest.c `flood_prep`): the leading valid-MAC1 initiations
    first, then the optional `control` (a valid initiation the mirror is not
    told of: it diverges the per-packet sequence, fail-closed, the
    merged-injection control), then `count` copies of the guest's invalid
    template (148 bytes: type 1, a MAC1 of 0xff; an environment fact). Each
    send is the producer, run exactly as a `wg_batch`'s inject items are
    (`batch`): `wg_packet_receive` in a `net_rx_action` section, B1's ring
    produce (`__ptr_ring_produce`: a full slot drops the packet and leaves
    the counter, receive.c:561-565), the counter's increment, the first
    packet's queue record; the worker consumes from the ring
    (`ptr_ring_consume_bh`, the batch rule) and ends at its first empty
    poll, where the C has it. The
    sends run inline in the trace task and the kworkers wait for the call to
    return, so a worker section between two producers' records mismatches.
    Then the deferred units, by the records (`afterBatch`): the receive
    worker drains the queue packet by packet, each with its own records (the
    under-load clock read at or over the threshold, receive.c:115; the decay
    read below it, :117; the `cond_resched` between packets, :216), and the
    handshake queue must be empty, the counter at zero, when the records end:
    a worker that outlives the guest's wait fails closed. Nothing is
    summarised, discarded or preset. The operation returns 0 (the submission
    succeeded). -/
def flood (count port family : Nat) (messages : List (List UInt8)) : M Int := do
  let some d := (← getWG).dev | unsupported "a flood to a port other than wg0's (no wg0)"
  if !d.running || port != d.incomingPort then unsupported "a flood to a port other than wg0's"
  for pid in d.peerList do requireNotPending pid "a flood while a handshake is queued"
  -- the guest's invalid template (harness/guest.c flood_prep)
  let invalid : List UInt8 := [1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0
  -- the flood's family: the fixture sender's v4-mapped destination (wg0 sees
  -- IPv4 from 127.0.0.1) or ::1 (IPv6, the ratelimiter's /64 table)
  let src ← senderSource family 0
  for msg in messages ++ List.replicate count invalid do
    -- lane C: each send's `udp_sendmsg` routes the datagram to loopback
    -- (the batch's inject arm likewise) and lo's one neighbour serves it
    if family == 4 then
      match ← Net.routeOutput4 0 src.daddr with
      | .error _ => invariant "wg_flood: the datagram to wg0's port has no route"
      | .ok r =>
        if r.dev != LO_IFINDEX || r.src != src.saddr then invariant "wg_flood: the route disagrees with the sender source"
        Net.neighbourClassify LO_IFINDEX
    fixtureSend
    runWorker .netRx do
      WG.wgReceive msg src
      pollScheduledInline
  afterBatch
  -- the receive worker drained the flood within the guest's wait (B4, 2.3:
  -- `afterBatch`'s drain check does not list the handshake queue)
  let d ← getDev
  requireDrained "the flood queued" [!d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  return 0

/-! ## W8: the creating namespace's teardown (docs/2026-10-06-w8-w9-netns-routing.md, 3.2) -/

/-- The section `cleanup_net` runs in `wg_netns_close`'s wait, after the
    pin's `__fput` queued it (`Syscalls.netnsClose`; `FS.fputFinal`'s pin
    hook, the C's last `put_net` at the nsfs dentry's eviction):
    `wg_netns_pre_exit` for wg0 (device.c, anchored), then the rest of the
    namespace's teardown, whose allocation outcomes are below the cut and
    which runs nothing else the mirror models. Exact in both record modes,
    as `dispatch` is for the device-level units: the unit must be pending
    (a run with none queued is a mirror invariant: before 2026-10-20 the
    placeholder run tore the namespace down whether or not the pin's release
    had queued it, campaign 2's namespace-pin finding); with records the
    section-start record names the queued unit (`peekUnit`, `resolveUnit`)
    and `runWorker` opens the section, clearing the PENDING bit; without
    records the placeholder section runs the same body. Fail-noisy: a
    section that did not open leaves the start record unmatched; a stop
    beyond the wait stays pending; a unit the queue record did not name is a
    hidden mismatch. The linkwatch event the carrier change queues is armed
    by no trace yet (W8b). -/
def netnsCleanup : M Unit := do
  if !(← getRouting).foreignCreator then unsupported "wg_netns_close outside the foreign-creator fixture"
  if !(← pendingDevice .netnsCleanup false) then
    invariant "cleanup_net: its section run with no unit queued (the pin's last release did not run)"
  if let some u ← peekUnit .netnsCleanup then _ ← resolveUnit .netnsCleanup u [0]
  runWorker .netnsCleanup do
    WG.netnsPreExit
    -- lane C: C's `lo` is unregistered by `default_device_exit_batch`
    -- (net/core/dev.c): `NETDEV_DOWN` (devinet's `ip_mc_down` flush, then
    -- `fib_disable_ip(lo, NETDEV_DOWN, false)`), then `NETDEV_UNREGISTER`
    -- (devinet's `inetdev_destroy` deleting `127.0.0.1/8` through the
    -- inetaddr chain, then `fib_disable_ip(lo, NETDEV_UNREGISTER, true)`),
    -- all on C's table; `fib_net_exit` frees it (a cut, the namespace exit)
    Net.Fib.inCreatorNs do
      Net.Fib.rtCacheFlush
      Net.Fib.netdevDown LO_IFINDEX
      Net.Fib.inetaddrDown LO_IFINDEX LOOPBACK4 8 true true
      Net.Fib.netdevUnregister LO_IFINDEX
    -- the rest of C's teardown: `sit0`'s unregister resets its tunnel's dst
    -- cache (net/ipv6/sit.c `ipip6_tunnel_uninit`: one kind-306 record, the
    -- only other consumer the section showed), and the notifications' and
    -- exits' allocations are below the cut (A)
    skipCut ([.dstCacheResetTs] ++ allocCuts)

/-! ## seccomp (docs/2026-10-12-seccomp-design.md, section 5): fixture knowledge and the two effects

The trace process starts as root with every capability, no-new-privs clear,
no mode, the `SIGSYS` handler installed by the guest at setup and
`RLIMIT_CORE` 0 (`Task`'s defaults). What the harness's own calls are, and
which of them fall inside a window, is fixture knowledge kept here. -/

/-- The trace process's fork: one `clone` (x86-64 56) at system-call entry
    inside the probe's window (design 6.2 rule 2; measured: no
    `rt_sigprocmask` around it in the guest's window). -/
def forkCalls : List Int := [56]

/-- The child leaves with `exit_group` (231), or with `exit` (60) when the
    probe asked for strict mode (harness/guest.c:1782 chooses by the request,
    not by the strict call's result; `exit_group` is not allowed under strict,
    design 2.9). Measured on sc2 (X): after a refused strict call the child
    still leaves with `exit`. -/
def childExitCall (strictRequested : Bool) : Int := if strictRequested then 60 else 231

/-- Harness calls whose entry falls inside the window after the operation's
    own call: none known yet. Stream W's measurement fixes this list (the
    KCOV-disable ioctl, 16, would be here if the guest read the area's count
    after it rather than before). -/
def windowTailCalls : List Int := []

/-- `copy_process`'s two clock reads (`start_time` at kernel/fork.c:2532,
    `start_boottime` at :2533) in the parent's window: consumed, not observed. -/
def forkClocks : AmbientM Unit := do
  _ ← hidden .forkStartTime
  _ ← hidden .forkStartBoottime

/-- The child of a child probe, from the parent by `copy_seccomp`'s effects
    (design 2.8, 4.1; `get_seccomp_filter`'s counts are the mirror's,
    `Seccomp.getSeccompFilter`, witnessed in the parent's window): the
    seccomp state, no-new-privs, the capability set and the action table
    copied; the pending set empty; the signal mask inherited. The child has
    no file table of its own: no modelled path in it touches a file. -/
def childCreate : TaskM Unit := do
  let p := (← getTasks).task
  let c : Task := { p with pending := 0, sigpending := false, taskWorks := [], inEventfd := false, exited := false }
  modifyTasks fun t => { t with child := some c }

/-- The child's exit: `seccomp_filter_release` (kernel/seccomp.c:572-585)
    runs after `kcov_task_exit`, in no window (design 2.8, audit C1): one
    `users` and one `refs` decrement on the head filter the child holds,
    nothing freed, since the parent holds it too; a task without a filter
    walks nothing. No decisions. -/
def childExit : Seccomp.M Unit := do
  match (← getTasks).child with
  | none => invariant "the child's exit effect without a child"
  | some c =>
    if let some id := c.seccomp.filter then
      match (← get).filters.get? id with
      | none => invariant s!"the child's head filter {id} is not allocated"
      | some f =>
        if f.users < 2 || f.refs < 2 then
          invariant s!"the child's exit would drop the parent's reference on filter {id}"
        modify fun s => { s with filters := s.filters.insert id { f with users := f.users - 1, refs := f.refs - 1 } }

/-- The parent's `wait4` reaped the child: its task object is dropped. -/
def childDrop : TaskM Unit := do
  if (← getTasks).child.isNone then invariant "wait4 without a child"
  modifyTasks fun t => { t with child := none }

/-- A `TRAP`'s delivery to the current task (design 2.2, 5): `get_signal`
    dequeues the `SIGSYS` (the pending set and `TIF_SIGPENDING` clear), the
    handler runs on its frame and `rt_sigreturn` restores the mask, which is
    as before. No decisions: the delivery side is not anchored. -/
def trapDelivered : TaskM Unit := do
  let t := (← getTasks).current
  modifyTask t fun tk => { tk with pending := sigdelset tk.pending SIGSYS, sigpending := false }

/-- The seccomp prefill fixture (`"seccomp_prefill": N`; design section 5)
    [USER 2026-10-12: queued]: the guest set no-new-privs and
    installed `N` copies of `Seccomp.Prefill.program` before the window. The
    initial task state carries that chain, reconstructed by the mirror's own
    translation of the same program and the decision-free cache emulation
    (`Leanux/Seccomp/Prefill.lean`): a fixture assumption, outside every
    window, like the fixture descriptors; the kernel's `total_insns` at the
    next recorded install is the evidence that the reconstruction's lengths
    are the kernel's. -/
def seccompPrefill (n : Nat) (sc : SeccompWorld) (t : TaskWorld) : Except String (SeccompWorld × TaskWorld) := Leanux.Seccomp.Prefill.apply n sc t

end Leanux.Env
