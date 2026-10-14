import Leanux.Proofs.WG.Lifetimes.BatchNapi
import Leanux.Proofs.WG.Lifetimes.EncryptWorker
import Leanux.Proofs.WG.Lifetimes.TxWorker
import Leanux.Proofs.WG.Lifetimes.ReceiveWorker

/-! Concrete scheduler activation boundaries. Internal source getters are
observed; scalar queue labels and record consumers remain exact lifted actions. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def activationHasWorkPrefix (a : Activation) : MixedM Bool := do
  let d ← liftPrefix getDev
  match a.worker with
  | .encryptWorker => return !d.encryptQueue.empty
  | .decryptWorker => return !d.decryptQueue.empty
  | .receiveWorker => return !d.handshakeQueue.isEmpty
  | .txWorker =>
    let some pid := a.pid | liftPrefix (invariant "a tx activation without its peer")
    let some item := (← getPeerMixed pid).txQueue.all.head? | return false
    let some id := item.head? | liftPrefix (invariant "an empty ring item")
    return (← getTxSkbPrefix id).state != .uncrypted
  | w => liftPrefix (invariant s!"{w.symbol} is not a draining worker")

def activationOccupancyPrefix (a : Activation) : MixedM Nat := do
  let d ← liftPrefix getDev
  match a.worker with
  | .encryptWorker => return d.encryptQueue.count
  | .decryptWorker => return d.decryptQueue.count
  | .receiveWorker => return d.handshakeQueue.length
  | .txWorker =>
    let some pid := a.pid | liftPrefix (invariant "a tx activation without its peer")
    return (← getPeerMixed pid).txQueue.all.length
  | w => liftPrefix (invariant s!"{w.symbol} is not a draining worker")

theorem activationHasWorkPrefix_erases (a : Activation) :
    ErasesPrefix (activationHasWorkPrefix a) (Env.Activation.hasWork a) := by
  unfold activationHasWorkPrefix Env.Activation.hasWork
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact getTxSkbPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationOccupancyPrefix_erases (a : Activation) :
    ErasesPrefix (activationOccupancyPrefix a) (Env.Activation.occupancy a) := by
  unfold activationOccupancyPrefix Env.Activation.occupancy
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationHasWorkPrefix_preserves (c : AmbientContracts I) (t : TxContracts I) (a : Activation) :
    PrefixPreserves I LifetimeEvent.Safe (activationHasWorkPrefix a) := by
  unfold activationHasWorkPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (t.get (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationOccupancyPrefix_preserves (c : AmbientContracts I) (a : Activation) :
    PrefixPreserves I LifetimeEvent.Safe (activationOccupancyPrefix a) := by
  unfold activationOccupancyPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem txWorkQueue_allocation (f : List PeerId → List PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  apply hi.congr
  · cases hr
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp [Option.bind_map, Function.comp_def]
  · exact metadata_modifyDev (fun d => {d with txWorkQueue := f d.txWorkQueue}) (fun _ => rfl) w x v hr

private theorem batchThrow_preserves (e : Stop) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (throw e : MixedM α) := by
  intro w h hi
  exact ⟨[], by simp, hi.safe, True.intro⟩

def cryptAheadPrefix (pid : PeerId) : MixedM Unit := do
  if (← liftPrefix get).hidden.isNone then return
  let some item := (← getPeerMixed pid).txQueue.all.head? | return
  let some id := item.head? | liftPrefix (invariant "an empty ring item")
  if (← getTxSkbPrefix id).state != .uncrypted then return
  if (← liftPrefix peekHiddenSite) != some HiddenSite.modTimerArm.info.id then return
  let w ← liftPrefix get
  let some enc := w.suspended.find? (·.worker == .encryptWorker)
    | throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is a timer arm (site 100)")
  liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
  let r ← encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p)) napiSoftirqPrefix
    (liftPrefix (Env.condResched .encryptWorker))
  liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid})
  match r with
  | .continued =>
    liftPrefix (modify fun s => {s with suspended := s.suspended.map fun x =>
      if x == enc then {x with iterations := x.iterations + 1} else x})
  | .ended => throw (.hidden "the encrypt activation's queue is empty, but the next record is a timer arm (site 100)")
  | .yielded => liftPrefix (invariant "the encrypt activation yielded on a record that is not a resched")

theorem cryptAheadPrefix_erases (pid : PeerId) : ErasesPrefix (cryptAheadPrefix pid) (Env.cryptAhead pid) := by
  unfold cryptAheadPrefix Env.cryptAhead
  repeat' first
    | with_reducible apply encryptIterPrefix_erases
    | with_reducible exact napiSoftirqPrefix_erases
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact getTxSkbPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_throw _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem cryptAheadPrefix_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (cryptAheadPrefix pid) := by
  unfold cryptAheadPrefix
  repeat' first
    | with_reducible apply encryptIterPrefix_allocation
    | with_reducible exact napiSoftirqPrefix_allocation
    | with_reducible exact txWorkQueue_allocation (fun q => q ++ [pid])
    | with_reducible exact txWorkQueue_allocation (fun q => q.erase pid)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (allocationTx.get (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ peekHiddenSite_sameKernel)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (condResched_sameKernel _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (by intro w x v hr; cases hr; rfl))
    | with_reducible exact batchThrow_preserves _
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def activationIterPrefix (a : Activation) : MixedM IterResult := do
  match a.worker with
  | .encryptWorker => encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p)) napiSoftirqPrefix (liftPrefix (Env.condResched .encryptWorker))
  | .txWorker =>
    let some pid := a.pid | liftPrefix (invariant "a tx activation without its peer")
    cryptAheadPrefix pid
    txIterPrefix pid (liftPrefix (Env.condResched .txWorker))
  | .decryptWorker => decryptIterPrefix napiSoftirqPrefix napiIrqExitPrefix (liftPrefix (Env.condResched .decryptWorker))
  | .receiveWorker => receiveIterPrefix (liftPrefix (Env.condResched .receiveWorker))
  | w => liftPrefix (invariant s!"{w.symbol} is not a draining worker")

theorem activationIterPrefix_erases (a : Activation) :
    ErasesPrefix (activationIterPrefix a) (Env.Activation.iter a) := by
  unfold activationIterPrefix Env.Activation.iter
  repeat' first
    | with_reducible apply cryptAheadPrefix_erases
    | with_reducible apply encryptIterPrefix_erases
    | with_reducible apply txIterPrefix_erases
    | with_reducible apply decryptIterPrefix_erases
    | with_reducible apply receiveIterPrefix_erases
    | with_reducible exact napiSoftirqPrefix_erases
    | with_reducible exact napiIrqExitPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationIterPrefix_allocation (a : Activation) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (activationIterPrefix a) := by
  unfold activationIterPrefix
  repeat' first
    | with_reducible exact cryptAheadPrefix_allocation _
    | with_reducible apply encryptIterPrefix_allocation
    | with_reducible apply txIterPrefix_allocation
    | with_reducible apply decryptIterPrefix_allocation
    | with_reducible apply receiveIterPrefix_preserves allocationAmbient allocationHandshakeReceive allocationReceiveQueue
    | with_reducible exact napiSoftirqPrefix_allocation
    | with_reducible exact napiIrqExitPrefix_allocation
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (condResched_sameKernel _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def activationRunPrefix (a : Activation) : MixedM Unit := do
  let occupancy ← activationOccupancyPrefix a
  let mut act := a
  for _ in [0:occupancy + 1] do
    match ← activationIterPrefix act with
    | .ended => _ ← liftPrefix (hidden (.sectionStop act.worker)); return
    | .continued => act := {act with iterations := act.iterations + 1}
    | .yielded =>
      liftPrefix (modify fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
      return
  liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run")

theorem activationRunPrefix_erases (a : Activation) :
    ErasesPrefix (activationRunPrefix a) (Env.Activation.run a) := by
  unfold activationRunPrefix Env.Activation.run
  repeat' first
    | with_reducible exact activationOccupancyPrefix_erases _
    | with_reducible exact activationIterPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationRunPrefix_allocation (a : Activation) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (activationRunPrefix a) := by
  unfold activationRunPrefix
  repeat' first
    | with_reducible exact activationOccupancyPrefix_preserves allocationAmbient _
    | with_reducible exact activationIterPrefix_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (hidden_sameKernel _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (by intro w x v hr; cases hr; rfl))
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.range _ _ _ allocationAmbient.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
