import Leanux.Proofs.WG.TimerDiscipline.WorkerReadyModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline.WorkerReady
open Leanux Leanux.WG Campaign2 Noise SendReady

theorem retainedPut_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount)
    (w : World) (device : w.wg.dev = some d) :
    (liftWG (peerPut (some pid))).run w = .ok ((), {w with
      wg := {w.wg with dev := some {d with peers := d.peers.insert pid {p with refcount := p.refcount - 1}}}
      ambient := {w.ambient with steps := retainedPutSteps p.refcount w.ambient.netRxSection w.ambient.steps}}) := by
  have positive : 0 < p.refcount := by omega
  have notOne : p.refcount ≠ 1 := by omega
  have notZero : p.refcount ≠ 0 := by omega
  have notUnder : ¬p.refcount < 1 := by omega
  have notOneB : (p.refcount == 1) = false := by simp [notOne]
  have notZeroB : (p.refcount == 0) = false := by simp [notZero]
  have nativeAmbient {α : Type} (action : AmbientM α) :
      (monadLift action : WG.M α) = StateT.lift action := rfl
  simp [liftWG, nativeAmbient, StateT.lift,peerPut, requireNotPending, refcountDecAndTest, branch, AmbientM.branch, branchCmp, AmbientM.branchCmp,
    getPeer, getDev, setPeer, modifyDev, resident, device,
    positive, notUnder, notOneB, notZeroB, retainedPutSteps,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get,
    modify, modifyGet, StateT.bind, StateT.pure, StateT.get, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, Except.pure]

theorem selection_named_run (pid headPid unit : Nat) (d : Device)
    (head : d.sendWorkQueue.head? = some headPid) (queued : pid ∈ d.sendWorkQueue)
    (start : List UInt8) (len : start.length = 16)
    (address : recordWordOf start 1 = unit) (nonnull : unit ≠ 0)
    (rest : List HiddenRecord) (w : World) (device : w.wg.dev = some d)
    (present : w.ambient.hidden = some ({site := (HiddenSite.sectionStart .sendWorker).info.id, bytes := start} :: rest))
    (resolved : w.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) =
      some (unit, Worker.sendWorker.index, pid)) :
    sendWorkerSelection.run w = .ok ((some unit, pid), w) := by
  have passive : HiddenSite.passive 40 = false := by decide
  change w.ambient.hidden = some ({site := 40, bytes := start} :: rest) at present
  change w.ambient.unitPeers.find? (fun e => e.1 == unit && e.2.1 == 0) = some (unit, 0, pid) at resolved
  have ambientProduct {α : Type} (action : AmbientM α) :
      (monadLift action : Leanux.M α) = liftAmbient action := rfl
  have wgProduct {α : Type} (action : WG.M α) :
      (monadLift action : Leanux.M α) = liftWG action := rfl
  simp [ambientProduct, wgProduct, liftWG, liftAmbient, sendWorkerSelection, getDev, peekUnit, AmbientM.peekUnit, AmbientM.skipAmbient, resolveUnit, AmbientM.resolveUnit,
    head, queued, len, address, nonnull, device, present, resolved, passive,
    HiddenSite.info, Worker.sectionId, Worker.index,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
    StateT.bind, StateT.pure, StateT.get, StateT.set, Except.bind, Except.pure]
  all_goals simp only [← present]

theorem dequeue_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pending : p.handshakePending = true)
    (w : World) (device : w.wg.dev = some d) :
    (sendWorkerDequeue pid).run w = .ok ((), {w with
      wg := {w.wg with dev := some (dequeuedSendDevice d pid p)}}) := by
  have wgProduct {α : Type} (action : WG.M α) :
      (monadLift action : Leanux.M α) = liftWG action := rfl
  simp [wgProduct, liftWG, sendWorkerDequeue, modifyDev, getPeer, getDev, setPeer,
    dequeuedSendDevice, resident, pending, device,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get,
    modify, modifyGet, StateT.bind, StateT.pure, StateT.get, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, Except.pure]

theorem start_run (bytes : List UInt8) (len : bytes.length = 16)
    (rest : List HiddenRecord) (w : World)
    (present : w.ambient.hidden = some ({site := (HiddenSite.sectionStart .sendWorker).info.id, bytes} :: rest)) :
    (hidden (.sectionStart .sendWorker) : Leanux.M _).run w = .ok (bytes,
      {w with ambient := {w.ambient with hidden := some rest, pendingWork := w.ambient.pendingWork.filter (· != Worker.sendWorker.index)}}) := by
  have passive : HiddenSite.passive 40 = false := by decide
  have drop : bytes.drop 16 = [] := by simp [← len]
  have take : bytes.take 16 = bytes := by simp [← len]
  have ambientProduct {α : Type} (action : AmbientM α) :
      (monadLift action : Leanux.M α) = liftAmbient action := rfl
  simp [ambientProduct, liftAmbient, hidden, AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, HiddenSite.info, Worker.sectionId, Worker.index,
    present, passive, len, drop, take,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set, modify, modifyGet,
    StateT.bind, StateT.pure, StateT.get, StateT.set, MonadStateOf.modifyGet,
    StateT.modifyGet, Except.bind, Except.pure]

theorem stop_run (bytes : List UInt8) (len : bytes.length = 8)
    (rest : List HiddenRecord) (w : World)
    (present : w.ambient.hidden = some ({site := (HiddenSite.sectionStop .sendWorker).info.id, bytes} :: rest)) :
    (hidden (.sectionStop .sendWorker) : Leanux.M _).run w = .ok (bytes, {w with ambient := {w.ambient with hidden := some rest}}) := by
  have passive : HiddenSite.passive 41 = false := by decide
  have drop : bytes.drop 8 = [] := by simp [← len]
  have take : bytes.take 8 = bytes := by simp [← len]
  have ambientProduct {α : Type} (action : AmbientM α) :
      (monadLift action : Leanux.M α) = liftAmbient action := rfl
  simp [ambientProduct, liftAmbient, hidden, AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, HiddenSite.info, Worker.sectionId, Worker.index,
    present, passive, len, drop, take,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
    StateT.bind, StateT.pure, StateT.get, StateT.set, Except.bind, Except.pure]

end Leanux.Proofs.WG.TimerDiscipline.WorkerReady
