import Leanux.Kernel.Defs
import Leanux.Kernel.TimerWheel

/-! Access to the WireGuard device state. A missing device, node or peer is a
    mirror invariant failure: the C never dereferences one that is not there. -/

namespace Leanux.WG
open Leanux

def getDev : M Device := do
  match (← getK).wg with
  | some d => return d
  | none => invariant "no WireGuard device in this trace's fixture"

def modifyDev (f : Device → Device) : M Unit :=
  modifyK fun k => { k with wg := k.wg.map f }

def getNode (id : NodeId) : M AipNode := do
  match (← getDev).nodes.get? id with
  | some n => return n
  | none => invariant s!"dangling allowedips node {id}"

def setNode (id : NodeId) (n : AipNode) : M Unit :=
  modifyDev fun d => { d with nodes := d.nodes.insert id n }

def freeNode (id : NodeId) : M Unit := do
  _ ← getNode id
  modifyDev fun d => { d with nodes := d.nodes.erase id }

def getPeer (id : PeerId) : M Peer := do
  match (← getDev).peers.get? id with
  | some p => return p
  | none => invariant s!"dangling peer {id}"

def setPeer (id : PeerId) (p : Peer) : M Unit :=
  modifyDev fun d => { d with peers := d.peers.insert id p }

def getKeypair (id : KeypairId) : M Keypair := do
  match (← getDev).keypairs.get? id with
  | some k => return k
  | none => invariant s!"dangling keypair {id}"

def setKeypair (id : KeypairId) (k : Keypair) : M Unit :=
  modifyDev fun d => { d with keypairs := d.keypairs.insert id k }

/-! ## The skb store (simulation-target review, section 4.2)

A packet on its way out or in is one object, owned once: the device ring, the
peer's `prev_queue`, a peeked head and a worker's local name it by its id, and
a publication (`PACKET_CB(skb)->state`) changes the one entry. `newTxSkb` is
the mirror's allocation point (the `PACKET_CB` assignments of
`wg_packet_send_staged_packets`), `freeTxSkb` its `kfree_skb` or its
consumption by the stack; `newRxSkb` is `wg_packet_consume_data`'s, `freeRxSkb`
the poll's `dev_kfree_skb` or `napi_gro_receive`. -/

def newTxSkb (p : DataPacket) : M SkbId := do
  let id := (← getDev).nextSkb
  modifyDev fun d => { d with txSkbs := d.txSkbs.insert id p, nextSkb := id + 1 }
  return id

def getTxSkb (id : SkbId) : M DataPacket := do
  match (← getDev).txSkbs.get? id with
  | some p => return p
  | none => invariant s!"dangling tx skb {id}"

def setTxSkb (id : SkbId) (f : DataPacket → DataPacket) : M Unit := do
  let p ← getTxSkb id
  modifyDev fun d => { d with txSkbs := d.txSkbs.insert id (f p) }

def freeTxSkb (id : SkbId) : M Unit := do
  let _ ← getTxSkb id   -- freeing twice is an invariant failure
  modifyDev fun d => { d with txSkbs := d.txSkbs.erase id }

def newRxSkb (p : RxPacket) : M SkbId := do
  let id := (← getDev).nextSkb
  modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id p, nextSkb := id + 1 }
  return id

def getRxSkb (id : SkbId) : M RxPacket := do
  match (← getDev).rxSkbs.get? id with
  | some p => return p
  | none => invariant s!"dangling rx skb {id}"

def setRxSkb (id : SkbId) (f : RxPacket → RxPacket) : M Unit := do
  let p ← getRxSkb id
  modifyDev fun d => { d with rxSkbs := d.rxSkbs.insert id (f p) }

def freeRxSkb (id : SkbId) : M Unit := do
  let _ ← getRxSkb id
  modifyDev fun d => { d with rxSkbs := d.rxSkbs.erase id }

/-- Retired (2026-10-14, the pre-release review's finding 3). It stopped a
    path that reads or changes state the pending handshake send worker also
    touches, on the ground that its outcome depended on when the worker ran.
    Since the dispatch-order capture, the worker runs exactly where its
    section records place it (`Leanux/Env/Batch.lean`'s scheduler), so a
    receive that the kernel ran before the queued send worker is determined:
    the pending work's effects apply at its section, not before. The stop
    excluded ordinary simultaneous initiation (a peer's initiation arriving
    while wg0's own is queued, `corpus/wireguard/p_sim_init_*`). A section
    record the scheduler cannot place is a hidden mismatch, as before. The
    callers remain for a later cleanup; `World.queuedThisCall` is no longer
    written (the Send audit's F7, 2026-10-15), its resets stay until the
    proof tree's frames over it are carried. -/
def requireNotPending (_pid : PeerId) (_what : String) : M Unit := pure ()

/-- Short-circuit `&&` and `||` over decisions: the right operand runs only
    when the left does not decide. (W3: moved here from `Netlink.lean`, so
    that `Handshake` no longer imports `Netlink`.) -/
def andM (a b : M Bool) : M Bool := do if ← a then b else pure false
def orM (a b : M Bool) : M Bool := do if ← a then pure true else b

/-- A little-endian 64-bit word of a record (`jiffies` is 64-bit from
    `INITIAL_JIFFIES` = 2^32 - 75000: never truncated). -/
def recordWord (bs : List UInt8) (k : Nat) : Nat :=
  ((bs.drop (8 * k)).take 8).foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The same word as the C's `unsigned long` (review item 8). -/
def recordWord64 (bs : List UInt8) (k : Nat) : UInt64 := (recordWord bs k).toUInt64

/-- The caller's `jiffies` read before a `mod_peer_timer` (pre-release
    review finding 2): kind 311 at `site`, consumed where the C evaluates the
    argument, before the guard; `none` without arm records. -/
def callerJiffies (site : HiddenSite) : M (Option UInt64) := do
  if (← getAmbient).armRecords then some <$> hiddenJiffies site else pure none

/-- `__mod_timer`'s placement once the base is forwarded to `clk` (B3,
    section 3.2, steps 4 to 6), with the kind-314 record consumed and
    checked when `unit?` is given (records on) and the peer's wheel invariant
    checked after. -/
def placeOnWheel (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit? : Option Nat) : M Unit := do
  let p ← getPeer pid
  match TimerWheel.place p t expires clk with
  | .kept _ =>
    -- :1123-1130: the slot, the list position and the stored bucket expiry
    -- stay; only `expires` changes. The C writes no enqueue record here.
    setPeer pid (p.setTimer t (some expires))
    if unit?.isSome then
      if (← peekHiddenSite) == some HiddenSite.timerEnqueue.info.id then
        throw (.hidden s!"Linux re-enqueued peer {pid}'s {repr t} timer, which the mirror keeps in its slot (expires {expires}, base clock {clk})")
  | .enqueued slot bexp =>
    if let some u := unit? then
      let eb ← hidden .timerEnqueue
      let (ridx, rbexp, u3) := (recordWord eb 0, recordWord64 eb 1, recordWord eb 2)
      if u != 0 && u3 != u then
        throw (.hidden s!"the enqueue record names timer {u3}, the arm record {u}")
      if ridx != slot || rbexp != bexp then
        throw (.hidden s!"wheel arithmetic differs from Linux for peer {pid}'s {repr t} timer: expires {expires}, base clock {clk}: the mirror puts it in slot {slot} at bucket expiry {bexp}, Linux in slot {ridx} at {rbexp}")
    -- the bucket expiry is in (expires, expires + 8^level] (calc_index rounds up)
    let lvl := TimerWheel.levelOf slot
    if !(timeAfter bexp expires && timeBeforeEq bexp (expires + (TimerWheel.LVL_GRAN lvl).toUInt64)) then
      invariant s!"a bucket expiry {bexp} outside (expires, expires + 8^{lvl}] for expires {expires}"
    let stamp := (← getK).timerEnqueues + 1
    modifyK fun k => { k with timerEnqueues := stamp }
    setPeer pid ((p.setTimer t (some expires)).setWheel t (some ⟨slot, bexp, stamp⟩))
  if let some what := TimerWheel.peerWheelProblem (← getPeer pid) then
    invariant s!"peer {pid}'s timers: {what}"

/-- D3 (docs/2026-10-05-d3-timers.md, sections 3.3 and 5.1): `mod_timer(&peer->
    timer_x, jiffies + delay)`, once `mod_peer_timer`'s guard has passed.
    With arm records (`World.armRecords`) the kind-303 record carries
    `mod_timer`'s own read `J_m` and `expires`. Review item 8
    (docs/2026-10-13-review-items-7-8.md, section 4) splits the rule into
    its two facts. The caller's read `J_c` is the source input and
    `expires = J_c + delay` exactly (timers.c:62,87,149,159,185,206,216),
    the caller's read `J_c` is its own record (kind 311, pre-release review
    finding 2), consumed before the guard; the mirror computes
    `expires = J_c + delay` and compares it with the published `e` (a
    mismatch is a wrong delay in the mirror, a hidden mismatch, by one
    tick or more). `J_m - J_c` is then an admissibility condition of the
    environment: a tick may land between the two reads, so the gap is 0
    or 1 on this one-CPU kernel; a negative gap cannot happen (the records
    would be inconsistent: a hidden mismatch); a gap above 1 is a stall
    between the reads, outside the fixture's timing domain, `unsupported`.
    `J_m` becomes the last known `jiffies`. All arithmetic is the C's, on
    `unsigned long`. Without records (the domain filter) the expiry is the
    nominal `jiffies + delay` from the last known `jiffies` (0 before any).

    B3 (docs/2026-10-15-design-b3-timer-wheel.md, section 3.2): then
    `__mod_timer` (timer.c:1065-1190) on the wheel. A pending timer re-armed
    with the same `expires` returns at once (:1085-1088): nothing else
    changes and no further record is consumed. Otherwise the C locks and
    forwards the base; its clock after the forward is the kind-313 record
    `{clk, timer}` (`HiddenSite.timerClk`), a hidden input (it depends on
    timers outside the modeled set, and inside a catch-up pass lags
    `jiffies` by up to the advance), checked fail-closed: at most one past
    `mod_timer`'s read (the lead of one after a pass, :2416), never behind
    the previous recorded clock (`__forward_timer_base` never rewinds,
    :994-1016), at or before the earliest overdue modeled bucket if one is
    pending (:1008-1014), and past the step of a pass this arm runs inside
    (`World.timerPassStep`). The slot and bucket expiry are
    `calc_wheel_index(expires, clk)` (`TimerWheel.calcWheelIndex`); the
    same-slot decision (:1123-1130) is computed from the peer's wheel entry,
    and the kind-314 record `{idx, bucket_expiry, timer}`
    (`HiddenSite.timerEnqueue`) checks it: it must be present, and equal to
    the mirror's slot and bucket expiry, exactly when the mirror decided to
    enqueue (:1144, :1173, :1180-1183), where the timer takes the next
    enqueue stamp (`hlist_add_head`, :659). The pending-iff-slotted
    invariant is checked after every arm (`TimerWheel.peerWheelProblem`). -/
def armTimer (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc? : Option UInt64 := none) : M Unit := do
  let w ← get
  if !(← getAmbient).armRecords then
    -- the domain filter (no records): the nominal expiry and the wheel at
    -- the last known `jiffies`, with no record to check
    let j0 := w.jiffiesLast.getD 0
    placeOnWheel pid t (j0 + delay.toUInt64) j0 none
    return
  let bs ← hidden .modTimerArm
  let (jm, e) := (recordWord64 bs 0, recordWord64 bs 1)
  -- the caller's read is recorded (kind 311), never recovered from `e`
  let some jc := jc? | invariant "a timer armed with arm records and no caller read (kind 311)"
  let expires := jc + delay.toUInt64       -- `expires = jiffies + delay`, the caller's arithmetic
  if expires != e then
    throw (.hidden s!"timer expiry differs from Linux: the caller read jiffies {jc} and mod_timer published {e}; the mirror's delay {delay} gives {expires}")
  let gap := (jm - jc).toInt64             -- `(long)(J_m - J_c)`
  if gap < 0 then
    throw (.hidden s!"mod_timer's jiffies {jm} is behind the caller's read {jc} (delay {delay}, expires {e})")
  if gap > 1 then
    unsupported s!"a stall between a timer's two jiffies reads (the mirror's delay matches the published expiry): the caller's {jc}, mod_timer's {jm} (delay {delay}, expires {e})"
  modify fun w => { w with jiffiesLast := some jm }
  -- dispatch order (docs/2026-10-11-dispatch-order.md): the record's
  -- third word is the timer's address, which its section names
  let u := recordWord bs 2
  if u != 0 then modify fun w => { w with timerUnits := (u, pid, t) :: w.timerUnits.filter (·.1 != u) }
  -- __mod_timer :1085-1088: a pending timer re-armed with the same expires
  if (← getPeer pid).timer t == some e then return
  -- the base locked and forwarded: kind 313, the base clock
  let cb ← hidden .timerClk
  let (clk, u2) := (recordWord64 cb 0, recordWord cb 1)
  if u != 0 && u2 != u then
    throw (.hidden s!"the base-clock record names timer {u2}, the arm record {u}")
  if timeAfter clk (jm + 1) then
    throw (.hidden s!"the timer base's clock {clk} is more than one past mod_timer's read {jm}")
  if let some prev := (← getK).timerClk then
    if timeBefore clk prev then
      throw (.hidden s!"the timer base's clock went back: {clk} after {prev}")
  if let some b := TimerWheel.earliestDue (← getDev) jm then
    if timeAfter clk b then
      throw (.hidden s!"the timer base's clock {clk} is past the overdue modeled bucket {b} (forward_timer_base stops at next_expiry)")
  if let some step := w.timerPassStep then
    if !timeAfter clk step then
      throw (.hidden s!"an arm inside a timer pass at step {step} with the base clock {clk} not past it")
  modifyK fun k => { k with timerClk := some clk }
  placeOnWheel pid t e clk (some u)

/-- `del_timer(&peer->timer_x)` (timer.c:1407-1430): detach if pending
    (`detach_if_pending`, :940-955): the expiry and the wheel entry go. -/
def delTimer (pid : PeerId) (t : PeerTimer) : M Unit := do
  let p ← getPeer pid
  setPeer pid ((p.setTimer t none).setWheel t none)

/-- L: the bound port of the socket `send4`/`send6` (socket.c:27-47, a cut)
    sends from: `wg->sock4` or `wg->sock6`. A send with that socket NULL (a
    worker racing `wg_stop`) is `-ENONET`, not modeled. -/
def socketPort (family : Nat) : M Nat := do
  let d ← getDev
  match (if family == AF_INET then d.sock4 else d.sock6) with
  | some port => return port
  | none => unsupported "a send while wg0's socket is NULL (-ENONET)"

/-- The system call sleeps: queued workers may run from here on. On this
    kernel (Tiny RCU, `CONFIG_PREEMPT_NONE`) `synchronize_net` does not
    sleep (docs/2026-10-05-l-lifecycle.md, section 2.2); the sleep points are
    `rcu_barrier`, `kthread_create`/`kthread_stop`, `flush_all_backlogs`,
    `msleep`, and the flushes when work is pending. -/
def mayHaveSlept : M Unit := modify fun w => { w with queuedThisCall := [] }

/-! ## The NET_RX softirq of a loopback transmission

wg0's datagrams (`send4`/`send6`, under `rcu_read_lock_bh`) and the ICMP
errors of `wg_xmit` (`icmp_ndo_send`, under `__dev_queue_xmit`'s
`rcu_read_lock_bh`) leave over loopback: `loopback_xmit` → `__netif_rx`
raises NET_RX with bottom halves disabled (`raise_softirq_irqoff` with
`in_interrupt()` true, so ksoftirqd is not woken: softirq.c:704-709). The
softirq runs at the `local_bh_enable` that ends the region:
`__local_bh_enable_ip` calls `do_softirq` when `!in_interrupt()` and a
softirq is pending (softirq.c:401-408), and nothing before it can run it
(an interrupt's exit sees `in_interrupt()`). So on the modeled paths, which
transmit only from process context, its section is **nested at the send
point, exactly once per raise**:
- `net_rx_action` polls the backlog until it is empty; the ICMP reply the
  delivery may produce (port unreachable) is queued to the same backlog
  while it is polled and handled in the same section;
- `handle_softirqs` defers to ksoftirqd only work that a softirq re-raised
  (a NAPI instance not completed), which a one- or two-packet backlog poll
  never leaves.
The section holds the delivery's own cut-site records (the reply's IP
ident, the flow-hash secret) and ambient records, and nothing else. A
record order other than this is a hidden-input mismatch (fail-closed), not
a lax skip. The D2 decrypt worker's NAPI poll is the case that may be
deferred to ksoftirqd (`Env.napiSoftirq`); if one were pending here, one
`net_rx_action` would poll both, which is outside the domain. -/

/-- The records a loopback delivery's NET_RX section may hold besides its
    start and stop: the ICMP reply's IP output (ident key and reserve, and
    its skb, `sock_alloc_send_pskb` via `ip_append_data`, an allocation cut
    site) and the flow dissector's hash secret. -/
def loopbackRxSites : List HiddenSite := [.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts

/-- `__netif_rx` → `____napi_schedule(backlog)` → `__raise_softirq_irqoff`:
    the pending bit. One transmission raises it once; the bit is clear on
    the modeled paths (each raise runs at its own `local_bh_enable`). -/
def raiseLoopbackRx : M Unit := do
  if (← get).netRxRaised then invariant "a loopback NET_RX raised while one is pending"
  modify fun w => { w with netRxRaised := true }

/-- The `local_bh_enable` that ends the transmitting region: the raised
    NET_RX runs here, in its own section (the records' `net_rx_action`
    start and stop, with `loopbackRxSites` between). Without records (the
    domain filter) the section is not read. -/
def loopbackSoftirq : M Unit := do
  if !(← get).netRxRaised then return
  if (← getDev).peers.toList.any (·.2.napiScheduled) then
    unsupported "a loopback NET_RX section while a NAPI poll is pending (one net_rx_action polls both)"
  modify fun w => { w with netRxRaised := false }
  if (← getAmbient).hidden.isNone then return
  let start := (HiddenSite.sectionStart .netRx).info
  if (← peekHiddenSite) != some start.id then
    let next := match ← peekHiddenSite with | some s => s!"site {s}" | none => "none"
    throw (.hidden s!"a loopback transmission raised NET_RX: expected its section ({start.label}, site {start.id}) at the send's local_bh_enable, the record is {next}")
  _ ← hidden (.sectionStart .netRx)
  skipCut loopbackRxSites
  _ ← hidden (.sectionStop .netRx)

/-- A loopback transmission's cut point: the IP output's cut-site records
    (`sites`, any number), then, if the packet left (`raised`), its NET_RX
    section at the region's end. -/
def loopbackSend (sites : List HiddenSite) (raised : Bool) : M Unit := do
  skipCut sites
  if raised then
    raiseLoopbackRx
    loopbackSoftirq

/-- `node->bit[i]`, `i` 0 or 1: the bounds-checked read that replaces
    `bit[..]!` in the trie code (future-proof-paths note, 3(d)); an index
    outside the pair is a mirror invariant failure, not a panic. -/
def AipNode.bitAt (n : AipNode) (i : Nat) : M (Option NodeId) :=
  match n.bit[i]? with
  | some c => pure c
  | none => invariant s!"allowedips node bit[{i}] is out of range"

/-- Read the pointer a slot holds (`*parent_bit`). -/
def slotGet (s : Slot) : M (Option NodeId) := do
  match s with
  | .root4 => return (← getDev).peerAllowedips.root4
  | .root6 => return (← getDev).peerAllowedips.root6
  | .child parent bit => (← getNode parent).bitAt bit

/-- Store a pointer into a slot (`rcu_assign_pointer(*parent_bit, node)`). -/
def slotSet (s : Slot) (v : Option NodeId) : M Unit := do
  match s with
  | .root4 => modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with root4 := v } }
  | .root6 => modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with root6 := v } }
  | .child parent bit =>
    let n ← getNode parent
    if bit > 1 then invariant "child slot bit beyond bit[2]"
    setNode parent { n with bit := n.bit.set! bit v }

end Leanux.WG
