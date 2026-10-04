import Leanux.WG.Device
import Leanux.WG.Receive
import Leanux.WG.Data

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
    destination, the sender's port, and the loopback interface (ifindex 1). -/
def senderSource (family : Nat) : M SkbSource :=
  if family == 4 then pure { family := 4, saddr := 0x7f000001, sport := SENDER_PORT, daddr := 0x7f000001, iif := 1 }
  else if family == 6 then pure { family := 6, saddr := 1, sport := SENDER_PORT, daddr := 1, iif := 1 }
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

/-- The IP packet `wg_xmit` receives from the fixture's sender: its 4-byte
    UDP datagram ("leux") behind a UDP header and an IPv4 or IPv6 header. -/
def xmitPacketLen (family : Nat) : Nat :=
  (if family == 4 then 20 else 40) + 8 + 4

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
      modify fun w => { w with senderInbox := w.senderInbox ++ [dg.bytes] }
    else match listenerFamily { family := dg.family, addr := dg.addr, port := dg.port } with
      | some 4 => modify fun w => { w with listenerV4 := w.listenerV4 ++ [dg.bytes] }
      | some _ => modify fun w => { w with listenerV6 := w.listenerV6 ++ [dg.bytes] }
      | none => if !loopback then unsupported "a datagram routed back into wg0"
  modify fun w => { w with sent := [] }

/-- Whether the kernel records dispatch sections: the `net-choice` kernel
    since the D1 sprint (stream A) opens one per dispatch of a function in
    the armed dispatch set (`harness/linux.py`, `DISPATCH_SYMBOLS`). -/
def SECTION_RECORDS : Bool := true

/-- A deferred unit's run: with section records, its section's start and
    stop records bracket it in the choice stream, so the order in which the
    kernel ran deferred units is checked rather than assumed. -/
def runWorker (w : Worker) (body : M Unit) : M Unit := do
  if SECTION_RECORDS then _ ← hidden (.sectionStart w)
  body
  if SECTION_RECORDS then _ ← hidden (.sectionStop w)

/-- The crypt work a deferred unit queued, on the kernel's one CPU after
    that unit: the encrypt worker (`packet_crypt_wq`, queued by
    `wg_packet_create_data`), then the tx worker of each peer it queued
    (`wg_queue_enqueue_per_peer_tx`), oldest first. What they send is
    delivered. -/
def runCryptWorkers : M Unit := do
  if !(← getDev).encryptQueue.isEmpty then runWorker .encryptWorker WG.encryptWorker
  for _ in [0:4096] do
    match (← getDev).txWorkQueue with
    | [] => deliverSent; return
    | pid :: rest =>
      modifyDev fun d => { d with txWorkQueue := rest }
      runWorker .txWorker (WG.txWorker pid)
      if !(← getDev).encryptQueue.isEmpty then invariant "the tx worker queued encryption"
  invariant "the tx work queue did not drain"

/-- A `cond_resched` in a worker: the crypt workers it woke run here iff the
    kernel ran them here, which the section records say (the next record is
    the encrypt worker's section start). A scheduling choice, captured. -/
def cryptYield : M Unit := do
  if (← peekHiddenSite) == some (HiddenSite.sectionStart .encryptWorker).info.id then runCryptWorkers

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
  let replies := w.senderInbox.map fun bs =>
    Lean.toJson [Lean.toJson bs.length, Lean.toJson (type bs), Lean.toJson (if bs.length ≥ 12 then WG.u32le bs 8 else 0),
                 Lean.toJson (hex bs)]
  let sortJson (xs : List Lean.Json) := (xs.toArray.qsort fun a b => a.compress < b.compress).toList
  modify fun w => { w with listenerV4 := [], listenerV6 := [], senderInbox := [] }
  let d ← getDev
  return (ret, Lean.Json.mkObj [
    ("datagrams", Lean.Json.arr (sortJson entries).toArray),
    ("replies", Lean.Json.arr (sortJson replies).toArray),
    ("stats", Lean.Json.mkObj [("tx_errors", Lean.toJson d.txErrors), ("tx_dropped", Lean.toJson d.txDropped)])])

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
  if !(← getDev).handshakeQueue.isEmpty then runWorker .receiveWorker (WG.handshakeReceiveWorker cryptYield)
  -- then the crypt work the receive worker queued (a session's keepalive)
  runCryptWorkers
  deliverSent
  return msg.length   -- udp_sendmsg returns the datagram's length

end Leanux.Env
