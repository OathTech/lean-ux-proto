import Leanux.Proofs.Logged.Workers

/-! Observers for committed activation execution. Consistency probes use the original action on a copied World. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Env

def napiSoftirqLogged : GhostM Unit := do
  let d ← getDev
  let pending := d.peers.toList.filterMap fun (pid, p) => if p.napiScheduled then some pid else none
  if pending.isEmpty then return
  if (← getWorld).hidden.isSome && (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  -- net_rx_action → napi_poll(n, &repoll) → n->poll(n, n->weight)
  runWorkerLogged .netRx do
    for pid in pending do
      discard <| rxPollLogged pid WG.NAPI_POLL_WEIGHT fun pkts => liftM (pkts.forM deliverInner)

theorem napiSoftirqLogged_erases : Erases (napiSoftirqLogged) (Env.napiSoftirq) := by
  unfold napiSoftirqLogged Env.napiSoftirq
  repeat' first
    | with_reducible apply runWorkerLogged_erases
    | with_reducible apply rxPollLogged_erases
    | ghost_step

def napiIrqExitLogged : GhostM Unit := do
  if (← getWorld).hidden.isNone then return
  if !(← getDev).peers.toList.any (·.2.napiScheduled) then return
  if (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let w ← getWorld
  let here := w.napiBeforePut.headD false
  setWorld { w with napiBeforePut := w.napiBeforePut.drop 1, napiAmbiguous := w.napiAmbiguous + 1 }
  if here then napiSoftirqLogged

theorem napiIrqExitLogged_erases : Erases (napiIrqExitLogged) (Env.napiIrqExit) := by
  unfold napiIrqExitLogged Env.napiIrqExit
  repeat' first
    | with_reducible apply napiSoftirqLogged_erases
    | ghost_step

/-- The committed repair iteration observes its original softirq callback
through `napiSoftirqLogged`; successful execution retains its acceptance events.
Copied-World consistency trials remain original
actions and discard their trial state rather than appending this history. -/
def cryptAheadLogged (pid : PeerId) : GhostM Unit := do
  if (← getWorld).hidden.isNone then return
  let some item := (← getPeer pid).txQueue.all.head? | return
  let some id := item.head? | invariant "an empty ring item"
  if (← getTxSkb id).state != .uncrypted then return
  let next ← peekHiddenSite
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let w ← getWorld
  let some enc := w.suspended.find? (·.worker == .encryptWorker)
    | throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  modifyDev fun d => { d with txWorkQueue := d.txWorkQueue ++ [pid] }
  let r ← encryptIterLogged checksumHelp napiSoftirqLogged (liftM (condResched .encryptWorker))
  modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.erase pid }
  match r with
  | .continued =>
    modifyWorld fun s => { s with suspended := s.suspended.map fun x =>
      if x == enc then { x with iterations := x.iterations + 1 } else x }
  | .ended => throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  | .yielded => invariant "the encrypt activation yielded on a record that is not a resched"

theorem cryptAheadLogged_erases (pid : PeerId) :
    Erases (cryptAheadLogged pid) (Env.cryptAhead pid) := by
  unfold cryptAheadLogged Env.cryptAhead
  repeat' first
    | with_reducible exact napiSoftirqLogged_erases
    | with_reducible apply encryptIterLogged_erases
    | ghost_step

def activationIterLogged (a : Activation) : GhostM IterResult := do
  match a.worker with
  | .encryptWorker => encryptIterLogged checksumHelp napiSoftirqLogged (liftM (condResched .encryptWorker))
  | .txWorker =>
    let some pid := a.pid | invariant "a tx activation without its peer"
    cryptAheadLogged pid
    txIterLogged pid (liftM (condResched .txWorker))
  | .decryptWorker => decryptIterLogged napiSoftirqLogged napiIrqExitLogged (liftM (condResched .decryptWorker))
  | .receiveWorker => workerIterLogged .receiveWorker none (liftM WG.receiveStep) (liftM (condResched .receiveWorker))
  | w => invariant s!"{w.symbol} is not a draining worker"

theorem activationIterLogged_erases (a : Activation) : Erases (activationIterLogged a) (Env.Activation.iter a) := by
  unfold activationIterLogged Env.Activation.iter
  repeat' first
    | with_reducible exact napiSoftirqLogged_erases
    | with_reducible exact napiIrqExitLogged_erases
    | with_reducible apply cryptAheadLogged_erases
    | with_reducible apply encryptIterLogged_erases
    | with_reducible apply txIterLogged_erases
    | with_reducible apply decryptIterLogged_erases
    | with_reducible apply workerIterLogged_erases
    | ghost_step

def activationRunLogged (a : Activation) : GhostM Unit := do
  let occupancy ← liftM (Activation.occupancy a)
  let mut act := a
  for _ in [0:occupancy + 1] do
    match ← activationIterLogged act with
    | .ended => _ ← hidden (.sectionStop act.worker); return
    | .continued => act := { act with iterations := act.iterations + 1 }
    | .yielded =>
      modifyWorld fun s => { s with suspended := s.suspended ++ [{ act with iterations := act.iterations + 1 }] }
      return
  invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run"

theorem activationRunLogged_erases (a : Activation) : Erases (activationRunLogged a) (Env.Activation.run a) := by
  unfold activationRunLogged Env.Activation.run
  repeat' first
    | with_reducible apply activationIterLogged_erases
    | ghost_step

def dispatchActivationLogged (w : Worker) : GhostM Bool := do
  let d ← getDev
  let mut pid : Option Nat := none
  match w with
  | .encryptWorker => if d.encryptQueue.empty then return false
  | .decryptWorker => if d.decryptQueue.empty then return false
  | .receiveWorker => if d.handshakeQueue.isEmpty then return false
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return false
    let p ← match ← peekUnit .txWorker with
      | some u => resolveUnit .txWorker u d.txWorkQueue
      | none => pure headPid
    modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.erase p }
    pid := some p
  | _ => return false
  _ ← hidden (.sectionStart w)
  activationRunLogged { worker := w, pid }
  return true

theorem dispatchActivationLogged_erases (w : Worker) : Erases (dispatchActivationLogged w) (Env.dispatch w) := by
  unfold dispatchActivationLogged Env.dispatch
  repeat' first
    | with_reducible apply activationRunLogged_erases
    | ghost_step

def scheduleLogged (stack : Option Worker := none) : GhostM Unit := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  for _ in [0:(← liftM recordBudget)] do
    if (← getWorld).hidden.isNone then
      let d ← getDev
      let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
        match w with
        | .receiveWorker => !d.handshakeQueue.isEmpty
        | .decryptWorker => !d.decryptQueue.empty
        | .encryptWorker => !d.encryptQueue.empty
        | _ => !d.txWorkQueue.isEmpty
      let some w := next | return
      if !(← dispatchActivationLogged w) then invariant s!"{w.symbol} has work but was not dispatched"
      continue
    let next ← peekHiddenSite
    if let some (w, true) := next.bind sectionOf then
      if ← dispatchActivationLogged w then continue else return
    if next == some netRx && (← getDev).peers.toList.any (·.2.napiScheduled) then
      napiSoftirqLogged
      if (← peekHiddenSite) == some netRx then return   -- left to the caller
      continue
    match ← liftM ((← getWorld).suspended.filterM Activation.consistent) with
    | [] => return
    | [a] =>
      if let some w := stack then
        if ← Activation.hasWork { worker := w } then
          unsupported "the records do not determine which suspended worker resumed"
      modifyWorld fun s => { s with suspended := s.suspended.filter (· != a) }
      activationRunLogged a
    | _ => unsupported "the records do not determine which suspended worker resumed"
  liftM (budgetExhausted "the scheduler loop")

theorem scheduleLogged_erases (stack : Option Worker) : Erases (scheduleLogged stack) (Env.schedule stack) := by
  unfold scheduleLogged Env.schedule
  repeat' first
    | with_reducible apply dispatchActivationLogged_erases
    | with_reducible apply napiSoftirqLogged_erases
    | with_reducible apply activationRunLogged_erases
    | ghost_step
  all_goals grind only [dispatchActivationLogged_erases, erases_liftM]

def nestedReschedLogged (self : Worker) : GhostM Unit := do
  if ← condResched self then scheduleLogged (stack := some self)

theorem nestedReschedLogged_erases (self : Worker) : Erases (nestedReschedLogged self) (Env.nestedResched self) := by
  unfold nestedReschedLogged Env.nestedResched
  repeat' first
    | with_reducible apply scheduleLogged_erases
    | ghost_step

def runCryptWorkersLogged : GhostM Unit := do
  scheduleLogged
  deliverSent

theorem runCryptWorkersLogged_erases : Erases runCryptWorkersLogged Env.runCryptWorkers := by
  unfold runCryptWorkersLogged Env.runCryptWorkers
  repeat' first | with_reducible exact scheduleLogged_erases _ | ghost_step

end Leanux.Proofs.Logged
