import Leanux.Kernel.Defs

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
    callers and `World.queuedThisCall` remain for a later cleanup. -/
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

/-- D3 (docs/2026-10-05-d3-timers.md, sections 3.3 and 5.1): `mod_timer(&peer->
    timer_x, jiffies + delay)`, once `mod_peer_timer`'s guard has passed.
    With arm records (`World.armRecords`) the kind-303 record carries
    `mod_timer`'s own read `J_m` and `expires`. Review item 8
    (docs/2026-10-13-review-items-7-8.md, section 4) splits the rule into
    its two facts. The caller's read `J_c` is the source input and
    `expires = J_c + delay` exactly (timers.c:62,87,149,159,185,206,216),
    so `J_c := expires - delay` is recovered from the record and the
    mirror's own delay, and the expiry the mirror stores is `J_c + delay`.
    `J_m - J_c` is then an admissibility condition of the environment: a
    tick may land between the two reads, so the gap is 0 or 1 on this
    one-CPU kernel. A negative gap cannot come from a stall (a stall only
    raises `J_m`): it is the mirror's delay being too small, a hidden
    mismatch (the D3-M8 channel). A gap above 1 is either a stall between
    the reads, outside the fixture's timing domain, or a delay too large;
    the record cannot tell them apart and it is reported as `unsupported`.
    `J_m` becomes the last known `jiffies`. All arithmetic is the C's,
    on `unsigned long`. Without records (the domain filter) the expiry is
    the nominal `jiffies + delay` from the last known `jiffies` (0 before
    any). `mod_timer` of a pending timer moves it (`__mod_timer`), so the
    field is overwritten. -/
def armTimer (pid : PeerId) (t : PeerTimer) (delay : Nat) : M Unit := do
  let w ← get
  let e ← if w.armRecords then
      let bs ← hidden .modTimerArm
      let (jm, e) := (recordWord64 bs 0, recordWord64 bs 1)
      let jc := e - delay.toUInt64          -- the caller's read, recovered
      let gap := (jm - jc).toInt64          -- `(long)(J_m - J_c)`
      if gap < 0 then
        throw (.hidden s!"timer expiry differs from Linux: mod_timer at jiffies {jm} to {e}, the mirror's delay is {delay} (the caller's read would be {jc}, after mod_timer's)")
      if gap > 1 then
        unsupported s!"a stall between a timer's two jiffies reads: the caller's {jc}, mod_timer's {jm} (delay {delay}, expires {e})"
      modify fun w => { w with jiffiesLast := some jm }
      -- dispatch order (docs/2026-10-11-dispatch-order.md): the record's
      -- third word is the timer's address, which its section names
      let u := recordWord bs 2
      if u != 0 then modify fun w => { w with timerUnits := (u, pid, t) :: w.timerUnits.filter (·.1 != u) }
      pure (jc + delay.toUInt64)            -- `expires = J_c + delay`, the record's by construction
    else pure (w.jiffiesLast.getD 0 + delay.toUInt64)
  setPeer pid ((← getPeer pid).setTimer t (some e))

/-- `del_timer(&peer->timer_x)` (timer.c:1407-1430): detach if pending. -/
def delTimer (pid : PeerId) (t : PeerTimer) : M Unit := do
  setPeer pid ((← getPeer pid).setTimer t none)

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
  if (← get).hidden.isNone then return
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
