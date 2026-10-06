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

/-- A path that reads or changes state the pending handshake worker also
    touches: its outcome depends on when the worker runs. Work queued earlier
    in this same system call, before it slept, has certainly not run
    (`CONFIG_PREEMPT_NONE`, one CPU), so such paths are determined. -/
def requireNotPending (pid : PeerId) (what : String) : M Unit := do
  if (← getPeer pid).handshakePending && !(← get).queuedThisCall.contains pid then
    unsupported s!"{what} races the pending handshake worker"

/-- The system call sleeps (`synchronize_net`, `flush_workqueue`): queued
    workers may run from here on. -/
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
    start and stop: the ICMP reply's IP output (ident key and reserve) and
    the flow dissector's hash secret. -/
def loopbackRxSites : List HiddenSite := [.ipIdentKey, .ipIdentReserve, .flowHashSecret]

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

/-- Read the pointer a slot holds (`*parent_bit`). -/
def slotGet (s : Slot) : M (Option NodeId) := do
  match s with
  | .root4 => return (← getDev).peerAllowedips.root4
  | .root6 => return (← getDev).peerAllowedips.root6
  | .child parent bit => return (← getNode parent).bit[bit]!

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
