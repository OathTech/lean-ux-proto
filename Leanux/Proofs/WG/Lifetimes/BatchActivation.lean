import Leanux.Proofs.WG.Lifetimes.BatchRefills
import Leanux.Proofs.WG.Lifetimes.BatchNapi
import Leanux.Proofs.WG.Lifetimes.EncryptWorker
import Leanux.Proofs.WG.Lifetimes.TxWorker
import Leanux.Proofs.WG.Lifetimes.ReceiveWorker

/-! Concrete scheduler activation boundaries. Internal source getters are
observed; scalar queue labels and record consumers remain exact lifted actions. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def activationHasWorkPrefix (a : Activation) : PrefixM LifetimeEvent Bool := do
  let d ← liftWGObserver (liftWGPrefix getDev)
  match a.worker with
  | .encryptWorker => return !d.encryptQueue.empty
  | .decryptWorker => return !d.decryptQueue.empty
  | .receiveWorker => return !d.handshakeQueue.empty
  | .txWorker =>
    let some pid := a.pid | liftPrefix (invariant "a tx activation without its peer")
    let some item := (← liftWGObserver (getPeerMixed pid)).txQueue.all.head? | return false
    let some id := item.head? | liftPrefix (invariant "an empty ring item")
    return (← liftWGObserver (getTxSkbPrefix id)).state != .uncrypted
  | w => liftPrefix (invariant s!"{w.symbol} is not a draining worker")

def activationOccupancyPrefix (a : Activation) : PrefixM LifetimeEvent Nat := do
  let d ← liftWGObserver (liftWGPrefix getDev)
  match a.worker with
  | .encryptWorker => return d.encryptQueue.count
  | .decryptWorker => return d.decryptQueue.count
  | .receiveWorker => return d.handshakeQueue.count
  | .txWorker =>
    let some pid := a.pid | liftPrefix (invariant "a tx activation without its peer")
    return (← liftWGObserver (getPeerMixed pid)).txQueue.all.length
  | w => liftPrefix (invariant s!"{w.symbol} is not a draining worker")

theorem activationHasWorkPrefix_erases (a : Activation) :
    ErasesPrefix (activationHasWorkPrefix a) (Env.Activation.hasWork a) := by
  unfold activationHasWorkPrefix Env.Activation.hasWork
  repeat' first
    | with_reducible exact liftWGObserver_erases (getPeerMixed_erases _)
    | with_reducible exact liftWGObserver_erases (getTxSkbPrefix_erases _)
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals first
    | exact liftWGObserver_erases (getPeerMixed_erases _)
    | exact liftWGObserver_erases (getTxSkbPrefix_erases _)
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)

theorem activationOccupancyPrefix_erases (a : Activation) :
    ErasesPrefix (activationOccupancyPrefix a) (Env.Activation.occupancy a) := by
  unfold activationOccupancyPrefix Env.Activation.occupancy
  repeat' first
    | with_reducible exact liftWGObserver_erases (getPeerMixed_erases _)
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals first
    | exact liftWGObserver_erases (getPeerMixed_erases _)
    | exact liftWGObserver_erases (getTxSkbPrefix_erases _)
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)

theorem activationHasWorkPrefix_preserves (c : ProductAmbientContracts I) (t : ProductTxContracts I) (a : Activation) :
    PrefixPreserves I LifetimeEvent.Safe (activationHasWorkPrefix a) := by
  unfold activationHasWorkPrefix
  repeat' first
    | with_reducible exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop (t.get (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev getDev_sameWGStore)
    | with_reducible exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev
    getDev_sameWGStore)

theorem activationOccupancyPrefix_preserves (c : ProductAmbientContracts I) (a : Activation) :
    PrefixPreserves I LifetimeEvent.Safe (activationOccupancyPrefix a) := by
  unfold activationOccupancyPrefix
  repeat' first
    | with_reducible exact ProductAmbientContracts.drop (c.getPeer (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev getDev_sameWGStore)
    | with_reducible exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev
    getDev_sameWGStore)

theorem txWorkQueue_allocation (f : List PeerId → List PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  apply hi.congr
  · cases hr
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp [Option.bind_map, Function.comp_def]
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (metadata_modifyDev (fun d => {d with txWorkQueue := f d.txWorkQueue}) (fun _ => rfl))
      w ambient x v ambient' hr

private theorem batchThrow_preserves (e : Stop) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (throw e : PrefixM LifetimeEvent α) := by
  intro w h hi
  exact ⟨[], by simp, hi.safe, True.intro⟩

def cryptAheadPrefix (pid : PeerId) : PrefixM LifetimeEvent Unit := do
  if (← liftPrefix getAmbient).hidden.isNone then return
  let some item := (← liftWGObserver (getPeerMixed pid)).txQueue.all.head? | return
  let some id := item.head? | liftPrefix (invariant "an empty ring item")
  if (← liftWGObserver (getTxSkbPrefix id)).state != .uncrypted then return
  let next ← liftPrefix peekHiddenSite
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let w ← liftPrefix getAmbient
  let some enc := w.suspended.find? (·.worker == .encryptWorker)
    | throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))
  let r ← encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p)) napiSoftirqPrefix
    (liftPrefix (Env.condResched .encryptWorker))
  liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))
  match r with
  | .continued =>
    liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended.map fun x =>
      if x == enc then {x with iterations := x.iterations + 1} else x})
  | .ended => throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  | .yielded => liftPrefix (invariant "the encrypt activation yielded on a record that is not a resched")

theorem cryptAheadPrefix_erases (pid : PeerId) : ErasesPrefix (cryptAheadPrefix pid) (Env.cryptAhead pid) := by
  unfold cryptAheadPrefix Env.cryptAhead
  repeat' first
    | with_reducible apply encryptIterPrefix_erases
    | with_reducible exact napiSoftirqPrefix_erases
    | with_reducible exact liftWGObserver_erases (getPeerMixed_erases _)
    | with_reducible exact liftWGObserver_erases (getTxSkbPrefix_erases _)
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_throw _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals first
    | exact liftWGObserver_erases (getPeerMixed_erases _)
    | exact liftWGObserver_erases (getTxSkbPrefix_erases _)
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)

theorem cryptAheadPrefix_allocation (pid : PeerId) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (cryptAheadPrefix pid) := by
  unfold cryptAheadPrefix
  repeat' first
    | with_reducible apply encryptIterPrefix_allocation
    | with_reducible exact napiSoftirqPrefix_allocation
    | with_reducible exact (txWorkQueue_allocation (fun q => q ++ [pid])).liftWGObserver
    | with_reducible exact (txWorkQueue_allocation (fun q => q.erase pid)).liftWGObserver
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).getPeer (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop ((ProductTxContracts.ofNative allocationTx).get (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) AmbientM.peekHiddenSite)
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store (fun _ => True) _ (condResched_sameKernel _))
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).invariant (fun _ => True) _)
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (get : AmbientM Ambient))
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store (fun _ => True) _ (by
        apply (ProjectedAction.iff_run _ _ _).mpr
        intro w x v hr
        cases hr
        rfl))
    | with_reducible exact batchThrow_preserves _
    | with_reducible exact PrefixPreserves.pure (ProductAmbientContracts.ofNative allocationAmbient).safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals first
    | exact (txWorkQueue_allocation (fun q => q ++ [pid])).liftWGObserver
    | exact (txWorkQueue_allocation (fun q => q.erase pid)).liftWGObserver
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) AmbientM.peekHiddenSite)
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store (fun _ => True) _ (by
        apply (ProjectedAction.iff_run _ _ _).mpr
        intro w x v hr
        cases hr
        rfl))

def activationIterPrefix (a : Activation) : PrefixM LifetimeEvent IterResult := do
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
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationIterPrefix_allocation (a : Activation) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (activationIterPrefix a) := by
  unfold activationIterPrefix
  repeat' first
    | with_reducible exact cryptAheadPrefix_allocation _
    | with_reducible apply encryptIterPrefix_allocation
    | with_reducible apply txIterPrefix_allocation
    | with_reducible apply decryptIterPrefix_allocation
    | with_reducible apply (receiveIterPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductHandshakeReceiveContracts.ofNative allocationHandshakeReceive) (ProductReceiveQueueContracts.ofNative allocationReceiveQueue))
    | with_reducible exact napiSoftirqPrefix_allocation
    | with_reducible exact napiIrqExitPrefix_allocation
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store (fun _ => True) _ (condResched_sameKernel _))
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure (ProductAmbientContracts.ofNative allocationAmbient).safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

def activationRunPrefix (a : Activation) : PrefixM LifetimeEvent Unit := do
  let occupancy ← activationOccupancyPrefix a
  let refills ← activationRefillsPrefix
  let mut act := a
  for _ in [0:occupancy + refills + 1] do
    match ← activationIterPrefix act with
    | .ended => _ ← liftPrefix (hidden (.sectionStop act.worker)); return
    | .continued => act := {act with iterations := act.iterations + 1}
    | .yielded =>
      liftPrefix (modifyAmbient fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]})
      return
  liftPrefix (invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) plus the refills its run could take ({refills})")

theorem activationRunPrefix_erases (a : Activation) :
    ErasesPrefix (activationRunPrefix a) (Env.Activation.run a) := by
  unfold activationRunPrefix Env.Activation.run
  repeat' first
    | with_reducible exact activationRefillsPrefix_erases
    | with_reducible exact activationOccupancyPrefix_erases _
    | with_reducible exact activationIterPrefix_erases _
    | with_reducible exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationRunPrefix_allocation (a : Activation) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (activationRunPrefix a) := by
  unfold activationRunPrefix
  repeat' first
    | with_reducible exact activationRefillsPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient)
    | with_reducible exact activationOccupancyPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) _
    | with_reducible exact activationIterPrefix_allocation _
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.hidden _))
    | with_reducible exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).invariant (fun _ => True) _)
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (get : AmbientM Ambient))
    | exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store (fun _ => True) _ (by
        apply (ProjectedAction.iff_run _ _ _).mpr
        intro w x v hr
        cases hr
        rfl))
    | with_reducible exact PrefixPreserves.pure (ProductAmbientContracts.ofNative allocationAmbient).safe _
    | with_reducible apply PrefixPreserves.range _ _ _ (ProductAmbientContracts.ofNative allocationAmbient).safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

  all_goals exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.hidden _))

end Leanux.Proofs.WG.Lifetimes
