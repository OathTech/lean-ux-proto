import Leanux.WG.Device
import Leanux.WG.Data
import Leanux.WG.RxData
import Leanux.Env.IpStack
import Leanux.Env.Stack

/-!
# Deferred units: dispatch sections and the scheduler's choices

Split out of `Leanux/Env.lean` at the interface commit (docs/2026-10-11-interface.md);
W7 phase 2 (docs/2026-10-06-w4-w7-transmit-bulk.md 17.15, the simulation-target
review's rank 6) made it the scheduler. This file holds what every runner
shares: a unit's section (`runWorker`), the section sites (`sectionOf`), the
draining workers' activations (`Activation`, in `World.suspended`) and the
NAPI poll's placements (`napiSoftirq`, `napiIrqExit`) and the scheduler loop
that dispatches and resumes the activations by the records (`schedule`,
`condResched`, `nestedResched`). `Env.lean` keeps the runners that deliver
over the loopback (`runCryptWorkers`, `runSendWorkers`, `afterBatch`) and so
stay with the fixture.
-/

namespace Leanux.Env
open Leanux Leanux.WG

/-- A deferred unit's run, for the units that run to their end without a
    `cond_resched` (the handshake send worker, the clear work, a timer
    callback, a softirq, `cleanup_net`); the draining workers, which yield,
    run as activations (`schedule`). The kernel (the `net-choice` profile
    since the D1 sprint) opens a dispatch section per dispatch of a function
    in the armed set (`harness/linux.py`, `DISPATCH_SYMBOLS`); its start and
    stop records bracket it in the choice stream, so the order in which the
    kernel ran deferred units is checked rather than assumed. -/
def runWorker (w : Worker) (body : M Unit) : M Unit := do
  _ ← hidden (.sectionStart w)
  -- W7 stream H (13.2 (ii)): a NET_RX section's steps carry its ordinal in
  -- the operation, the count of section starts consumed so far
  -- (`noteNetRxStart`, advanced by the `hidden` above); a softirq never
  -- nests in a softirq, so the ordinal is cleared at its end
  if w == .netRx then modifyAmbient fun s => { s with netRxSection := s.netRxSections }
  body
  if w == .netRx then modifyAmbient fun s => { s with netRxSection := 0 }
  _ ← hidden (.sectionStop w)

/-- An item of `wg_batch` (W7, section 5.5): a datagram the fixture's sender
    submits in one `io_uring_enter`, to wg0's port (`inject`) or into wg0
    (`xmit`, as `wg_xmit`'s packet). -/
inductive BatchItem where
  | inject (family port : Nat) (message : List UInt8)
  | xmit (family addr : Nat) (payload : List UInt8) (opts : XmitOpts)
  deriving Repr

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
    one CPU (`CONFIG_PREEMPT_NONE`): whether the kernel switched away. A
    scheduling choice, recorded: the kernel writes a resched record when
    `__cond_resched` is about to schedule. What it ran then, and when this
    worker resumed, is the scheduler loop's reading of the records that
    follow (`schedule`); the worker's activation is suspended meanwhile. -/
def condResched (self : Worker) : M Bool := do
  let some site := self.resched? | invariant s!"{self.symbol} has no cond_resched"
  if (← peekHiddenSite) != some site.info.id then return false
  _ ← hidden site
  return true

/-- The delivery of an inner packet that GRO flushed at `napi_complete_done`
    (a cut point): the receive-side stack model, `Leanux/Env/Stack.lean`
    (W5+W6), decides fail-closed what Linux does with it. -/
def deliverInner (pkt : List UInt8) : M Unit := Stack.receive pkt

/-- The NET_RX softirq the decrypt worker's `napi_schedule` raised
    (`____napi_schedule` → `raise_softirq_irqoff` outside `net_rx_action`,
    which wakes ksoftirqd), placed by the records (design section 5). The
    hook is called at the decrypt worker's loop head and after its enqueue,
    and at the encrypt worker's loop head (its `ptr_ring_consume_bh`,
    send.c:293, the first `spin_unlock_bh` of the worker the kernel may
    switch to at the decrypt worker's `cond_resched` while the poll is still
    pending: design 17.17); it runs the poll iff a poll is pending and the
    next record starts a NET_RX section:
    - (a) ksoftirqd: the worker switched away at its `cond_resched` (a
      resched record, consumed by `condResched`, which stops at a NET_RX
      start), and ksoftirqd ran the softirq in a top-level section;
    - (b) inline: the worker's next `spin_unlock_bh` (`ptr_ring_consume_bh`)
      ran it, nested in the worker's section, with no resched record; or,
      after the decrypt worker's switch, the encrypt worker's first ring
      poll ran it, nested in the encrypt worker's section before its first
      item's records;
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
  if (← getAmbient).hidden.isSome && (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
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
  if (← getAmbient).hidden.isNone then return
  if !(← getDev).peers.toList.any (·.2.napiScheduled) then return
  if (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let w ← get
  let here := w.napiBeforePut.headD false
  set { w with napiBeforePut := w.napiBeforePut.drop 1, napiAmbiguous := w.napiAmbiguous + 1 }
  if here then napiSoftirq

/-- Whether the activation's loop condition holds: its ring or queue has an
    item it would process when it resumes (the tx worker's: a head it can
    send, send.c:269-272). -/
def Activation.hasWork (a : Activation) : M Bool := do
  let d ← getDev
  match a.worker with
  | .encryptWorker => return !d.encryptQueue.empty
  | .decryptWorker => return !d.decryptQueue.empty
  | .receiveWorker => return !d.handshakeQueue.empty
  | .txWorker =>
    let some pid := a.pid | invariant "a tx activation without its peer"
    let some item := (← getPeer pid).txQueue.all.head? | return false
    let some id := item.head? | invariant "an empty ring item"
    return (← getTxSkb id).state != .uncrypted
  | w => invariant s!"{w.symbol} is not a draining worker"

/-- The encrypt worker's yield position, by elimination (claim-point
    robustness, 2026-10-13; docs/2026-10-06-w4-w7-transmit-bulk.md 17.18).
    The encrypt worker's loop reads no record per item (encryption has no
    hidden input, and the tx work's queue record is written once, at the
    first enqueue of a not-pending unit), so its resched record says that it
    yielded, not after how many items; the mirror's activation yields at the
    first `cond_resched` that sees the record. That is exact while nothing
    runs between the yield and the resumption, and wrong when the records
    then dispatch the tx worker, which sends every item the kernel's encrypt
    worker had crypted before yielding: its section carries one record group
    per item (the persistent keepalive's caller read, kind 311, then its arm,
    `wg_timers_any_authenticated_packet_traversal`, are the first records of
    each), so the kernel's count is in the records. Hence, when the tx
    worker's head is still uncrypted in the mirror and the next record is
    that caller read or arm rather than the tx section's stop, the suspended
    encrypt activation crypted that item before its yield: one encrypt
    iteration runs here, consuming no record (its `cond_resched` sees the
    read, not a resched), and the tx step then sends the item. Fail-closed:
    no suspended encrypt activation, or an empty encrypt queue, with the
    read or arm next is a hidden mismatch; an item whose
    encryption would consume a record (another peer's first enqueue) stays
    a mismatch at that record. -/
def cryptAhead (pid : PeerId) : M Unit := do
  if (← getAmbient).hidden.isNone then return
  let some item := (← getPeer pid).txQueue.all.head? | return
  let some id := item.head? | invariant "an empty ring item"
  if (← getTxSkb id).state != .uncrypted then return
  let next ← peekHiddenSite
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let some enc := (← getAmbient).suspended.find? (·.worker == .encryptWorker)
    | throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  -- the item was crypted before the tx worker's dispatch, while its work was
  -- still pending (queued at the first enqueue): the enqueue's `queue_work`
  -- then wrote no record, so the unit is held queued for this iteration
  modifyDev fun d => { d with txWorkQueue := d.txWorkQueue ++ [pid] }
  let r ← WG.encryptIter checksumHelp napiSoftirq (condResched .encryptWorker)
  modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.erase pid }
  match r with
  | .continued =>
    modifyAmbient fun s => { s with suspended := s.suspended.map fun x =>
      if x == enc then { x with iterations := x.iterations + 1 } else x }
  | .ended => throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  | .yielded => invariant "the encrypt activation yielded on a record that is not a resched"

/-- One iteration of the activation's C loop: the worker's step and its
    `cond_resched` decision (`workerIter`). -/
def Activation.iter (a : Activation) : M IterResult := do
  match a.worker with
  | .encryptWorker => WG.encryptIter checksumHelp napiSoftirq (condResched .encryptWorker)
  | .txWorker =>
    let some pid := a.pid | invariant "a tx activation without its peer"
    cryptAhead pid
    WG.txIter pid (condResched .txWorker)
  | .decryptWorker => WG.decryptIter napiSoftirq napiIrqExit (condResched .decryptWorker)
  | .receiveWorker => workerIter .receiveWorker none WG.receiveStep (condResched .receiveWorker)
  | w => invariant s!"{w.symbol} is not a draining worker"

/-- The items the activation's loop can consume before it finds its queue
    empty: the queue's occupancy now (review item 7). The C loop runs while
    the ring or queue yields an item; on the modelled paths nothing refills a
    worker's own queue inside its run (refills happen while it is suspended,
    and each resumption is a new run), so a run makes at most one iteration
    per item present at its start, plus the poll that finds none. -/
def Activation.occupancy (a : Activation) : M Nat := do
  let d ← getDev
  match a.worker with
  | .encryptWorker => return d.encryptQueue.count
  | .decryptWorker => return d.decryptQueue.count
  | .receiveWorker => return d.handshakeQueue.count
  | .txWorker =>
    let some pid := a.pid | invariant "a tx activation without its peer"
    return (← getPeer pid).txQueue.all.length
  | w => invariant s!"{w.symbol} is not a draining worker"

/-- Run the activation from its loop position until its loop ends (its
    section stop, consumed where the records have it) or it yields
    (suspended, `World.suspended`). The fuel is derived from the state the
    loop drains (`Activation.occupancy`), so its exhaustion is a genuine
    invariant: more items consumed than were ever queued. -/
def Activation.run (a : Activation) : M Unit := do
  let occupancy ← Activation.occupancy a
  let mut act := a
  for _ in [0:occupancy + 1] do
    match ← Activation.iter act with
    | .ended => _ ← hidden (.sectionStop act.worker); return
    | .continued => act := { act with iterations := act.iterations + 1 }
    | .yielded =>
      modifyAmbient fun s => { s with suspended := s.suspended ++ [{ act with iterations := act.iterations + 1 }] }
      return
  invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run"

/-- Whether the records are consistent with the activation resuming now: its
    run from here, to its yield or its stop, on a copy of the world, reads
    them without a mismatch. A resumption leaves no record of its own, so
    the records name it by what the resumed worker reads next; this is the
    elimination among the suspended activations (`schedule`). -/
def Activation.consistent (a : Activation) : M Bool := do
  match (Activation.run a).run (← get) with
  | .ok _ => return true
  | .error (.hidden _) => return false
  | .error e => throw e

/-- The unit of worker `w` whose section the next record starts, when it has
    work: a new activation, dispatched (`process_one_work`; the tx worker the
    record names leaves the work queue, docs/2026-10-11-dispatch-order.md)
    and run. `false` when the unit has no work: the record is not this
    dispatch, and mismatches in the consumer that meets it. -/
def dispatch (w : Worker) : M Bool := do
  let d ← getDev
  let mut pid : Option Nat := none
  match w with
  | .encryptWorker => if d.encryptQueue.empty then return false
  | .decryptWorker => if d.decryptQueue.empty then return false
  | .receiveWorker => if d.handshakeQueue.empty then return false
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return false
    let p ← match ← peekUnit .txWorker with
      | some u => resolveUnit .txWorker u d.txWorkQueue
      | none => pure headPid
    modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.erase p }
    pid := some p
  | _ => return false
  _ ← hidden (.sectionStart w)
  Activation.run { worker := w, pid }
  return true

/-- The scheduler loop (W7 phase 2, design 17.15): the schedule of the
    deferred units, read from the records. Each turn reads the next record
    and runs what it names:
    - a section start of a draining worker with work: a new activation
      (`dispatch`), run until it yields or ends;
    - a NET_RX section while a NAPI poll is pending: the poll ksoftirqd ran
      at a yield (D2's order (a), `napiSoftirq`);
    - else the suspended activation whose resumption the records are
      consistent with (`Activation.consistent`), by elimination: one, and it
      resumes (its own stop record, when its queue is empty, ends it); none,
      and the loop ends at a record it does not run (the caller's: a send
      worker, a timer, the operation's end); several, and the records do not
      determine the kernel's choice: fail-closed.
    A worker the caller holds on the mirror's own stack (`stack`: the flood's
    receive worker, whose section the flood manages) resumes when the loop
    ends; with work of its own it is a candidate too, and a consistent
    suspended one beside it is the same undetermined choice.
    Without records (the domain filter, which runs before Linux) nothing
    yields and the order is fixed: the receive worker, the decrypt worker,
    the encrypt worker, then each queued tx worker. -/
def schedule (stack : Option Worker := none) : M Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  -- record-driven (review item 7): every turn consumes a record (a section
  -- start, a NET_RX section, a resumption's records) or returns; without
  -- records the filter's bound
  for _ in [0:(← recordBudget)] do
    if (← getAmbient).hidden.isNone then
      let d ← getDev
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.empty
        | .decryptWorker => !d.decryptQueue.empty
        | .encryptWorker => !d.encryptQueue.empty
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← dispatch w) then invariant s!"{w.symbol} has work but was not dispatched"
      continue
    let next ← peekHiddenSite
    if let some (w, true) := next.bind sectionOf then
      if ← dispatch w then continue else return
    if next == some netRx && (← getDev).peers.toList.any (·.2.napiScheduled) then
      napiSoftirq
      if (← peekHiddenSite) == some netRx then return   -- left to the caller
      continue
    match ← (← getAmbient).suspended.filterM Activation.consistent with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← Activation.hasWork { worker := w } then
          unsupported "the records do not determine which suspended worker resumed"
      modifyAmbient fun s => { s with suspended := s.suspended.filter (· != a) }
      Activation.run a
    | _ => unsupported "the records do not determine which suspended worker resumed"
  budgetExhausted "the scheduler loop"

/-- `cond_resched()` in a worker the environment runs on the mirror's own
    stack (the flood's receive worker, `Env.flood`, whose section the flood
    manages around `workerLoop`): at a switch the scheduler runs what the
    records name, and the worker resumes when the loop ends. -/
def nestedResched (self : Worker) : M Unit := do
  if ← condResched self then schedule (stack := some self)

end Leanux.Env
