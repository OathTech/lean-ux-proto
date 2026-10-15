import Leanux.Proofs.WG.Queues.RxWorkerHistory

/-! The transmit pre-step and one activation iteration retain concrete NAPI
callbacks in the persistent journal. Poll-free TX bodies retain their existing
lifetime focus; the receive-worker adapter also records actual session cuts.
Scheduler loops and copied trials are not covered here. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

private theorem throw_allocation (e : Stop) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (throw e : MixedM α) := by
  intro w h hi
  exact ⟨[], by simp, hi.safe, True.intro⟩

private theorem encrypt_allocation : PrefixPreserves AllocationInv LifetimeEvent.Safe
    (encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p)) napiSoftirqPrefix
      (liftPrefix (Env.condResched .encryptWorker))) :=
  encryptIterPrefix_allocation napiSoftirqPrefix_allocation
    (allocation_kernel _ (condResched_sameKernel _))

def cryptAhead (pid : PeerId) : Obs Unit := do
  if (← mixed (liftPrefix get)).hidden.isNone then return
  let some item := (← mixed (getPeerMixed pid)).txQueue.all.head? | return
  let some id := item.head? | mixed (liftPrefix (invariant "an empty ring item"))
  if (← mixed (getTxSkbPrefix id)).state != .uncrypted then return
  let next ← mixed (liftPrefix peekHiddenSite)
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let w ← mixed (liftPrefix get)
  let some enc := w.suspended.find? (·.worker == .encryptWorker)
    | mixed (throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  mixed (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}))
  let r ← encryptIteration
  mixed (liftPrefix (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue.erase pid}))
  match r with
  | .continued =>
    mixed (liftPrefix (modify fun s => {s with suspended := s.suspended.map fun x =>
      if x == enc then {x with iterations := x.iterations + 1} else x}))
  | .ended => mixed (throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)"))
  | .yielded => mixed (liftPrefix (invariant "the encrypt activation yielded on a record that is not a resched"))

theorem cryptAhead_erases (pid : PeerId) : ErasesPrefix (cryptAhead pid) (Env.cryptAhead pid) := by
  unfold cryptAhead Env.cryptAhead
  repeat' first
    | with_reducible exact encryptIteration_erases
    | with_reducible exact mixed_erases (getPeerMixed_erases _)
    | with_reducible exact mixed_erases (getTxSkbPrefix_erases _)
    | with_reducible exact mixed_erases (erasesPrefix_lift _)
    | with_reducible exact mixed_erases (erasesPrefix_throw _)
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem cryptAhead_preserves (pid : PeerId) :
    PrefixPreserves BoundaryInv BoundarySafe (cryptAhead pid) := by
  unfold cryptAhead
  repeat' first
    | with_reducible exact encryptIteration_preserves
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply mixed_preserves
    | with_reducible exact txWorkQueue_allocation (fun q => q ++ [pid])
    | with_reducible exact txWorkQueue_allocation (fun q => q.erase pid)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (allocationTx.get (fun _ => True) _)
    | with_reducible exact allocation_kernel _ peekHiddenSite_sameKernel
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact throw_allocation _
    | exact allocation_kernel _ (by intro w x v hr; cases hr; rfl)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem cryptAhead_projects (pid : PeerId) :
    ProjectsUnder AuditInv auditEvent (cryptAhead pid) (auditFocus (cryptAheadPrefix pid)) := by
  unfold cryptAhead cryptAheadPrefix
  repeat' first
    | with_reducible exact encryptIteration_projects
    | with_reducible exact encrypt_allocation
    | with_reducible exact projectsFocus_pure _
    | with_reducible apply mixed_projects
    | with_reducible apply projectsFocus_bind
    | with_reducible exact txWorkQueue_allocation (fun q => q ++ [pid])
    | with_reducible exact txWorkQueue_allocation (fun q => q.erase pid)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (allocationTx.get (fun _ => True) _)
    | with_reducible exact allocation_kernel _ peekHiddenSite_sameKernel
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact throw_allocation _
    | exact allocation_kernel _ (by intro w x v hr; cases hr; rfl)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

private theorem tx_allocation (pid : PeerId) : PrefixPreserves AllocationInv LifetimeEvent.Safe
    (txIterPrefix pid (liftPrefix (Env.condResched .txWorker))) :=
  txIterPrefix_allocation pid (allocation_kernel _ (condResched_sameKernel _))

private theorem receive_allocation : PrefixPreserves AllocationInv LifetimeEvent.Safe
    (receiveIterPrefix (liftPrefix (Env.condResched .receiveWorker))) :=
  receiveIterPrefix_preserves allocationAmbient allocationHandshakeReceive allocationReceiveQueue
    (allocation_kernel _ (condResched_sameKernel _))

def activationIteration (a : Activation) : Obs IterResult := do
  match a.worker with
  | .encryptWorker => encryptIteration
  | .txWorker =>
    let some pid := a.pid | mixed (liftPrefix (invariant "a tx activation without its peer"))
    cryptAhead pid
    mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))
  | .decryptWorker => decryptIteration
  | .receiveWorker => Origins.HistoryAdapters.receiveIteration
  | w => mixed (liftPrefix (invariant s!"{w.symbol} is not a draining worker"))

theorem activationIteration_erases (a : Activation) :
    ErasesPrefix (activationIteration a) (Env.Activation.iter a) := by
  unfold activationIteration Env.Activation.iter
  repeat' first
    | with_reducible exact encryptIteration_erases
    | with_reducible exact decryptIteration_erases
    | with_reducible exact cryptAhead_erases _
    | with_reducible exact mixed_erases (txIterPrefix_erases _ (erasesPrefix_lift _))
    | with_reducible exact Origins.HistoryAdapters.receiveIteration_erases
    | with_reducible exact mixed_erases (erasesPrefix_lift _)
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationIteration_preserves (a : Activation) :
    PrefixPreserves BoundaryInv BoundarySafe (activationIteration a) := by
  unfold activationIteration
  repeat' first
    | with_reducible exact encryptIteration_preserves
    | with_reducible exact decryptIteration_preserves
    | with_reducible exact cryptAhead_preserves _
    | with_reducible exact mixed_preserves (tx_allocation _)
    | with_reducible exact Origins.HistoryAdapters.receiveIteration_preserves
    | with_reducible exact mixed_preserves (AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _))
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem activationIteration_projects (a : Activation) :
    ProjectsUnder AuditInv auditEvent (activationIteration a) (auditFocus (activationIterPrefix a)) := by
  unfold activationIteration activationIterPrefix
  repeat' first
    | with_reducible exact encryptIteration_projects
    | with_reducible exact decryptIteration_projects
    | with_reducible exact cryptAhead_projects _
    | with_reducible exact cryptAheadPrefix_allocation _
    | with_reducible exact tx_allocation _
    | with_reducible exact mixed_projects (tx_allocation _)
    | with_reducible exact Origins.HistoryAdapters.receiveIteration_projects
    | with_reducible exact mixed_projects (AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _))
    | with_reducible apply projectsFocus_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
