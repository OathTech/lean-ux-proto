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

/-- D3 (docs/2026-10-05-d3-timers.md, section 5.1): `mod_timer(&peer->timer_x,
    jiffies + delay)`, once `mod_peer_timer`'s guard has passed. With arm
    records (`World.armRecords`) the expiry is the kind-303 record's, checked
    against `delay` (stream M); without them it is the nominal
    `jiffies + delay` from the last recorded `jiffies` (0 before any), which
    nothing reads: firing stays outside the domain (`Timing.timerMayExpire`). -/
def armTimer (pid : PeerId) (t : PeerTimer) (delay : Nat) : M Unit := do
  if (← get).armRecords then
    unsupported "D3 stream M: not yet (consuming the kind-303 arm record)"
  let j := (← get).jiffiesLast.getD 0
  setPeer pid ((← getPeer pid).setTimer t (some (j + delay)))

/-- `del_timer(&peer->timer_x)` (timer.c:1407-1430): detach if pending. -/
def delTimer (pid : PeerId) (t : PeerTimer) : M Unit := do
  setPeer pid ((← getPeer pid).setTimer t none)

/-- The system call sleeps (`synchronize_net`, `flush_workqueue`): queued
    workers may run from here on. -/
def mayHaveSlept : M Unit := modify fun w => { w with queuedThisCall := [] }

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
