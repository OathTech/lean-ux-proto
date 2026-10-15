import Leanux.Proofs.WG.TimerDiscipline.SendDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchFrames
import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationBridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Original head/named selection, before the dequeue. -/
def sendWorkerSelection : M (Option Nat × PeerId) := do
  let d ← getDev
  let some headPid := d.sendWorkQueue.head? | invariant "no queued handshake send work"
  let named ← peekUnit .sendWorker
  let pid ← match named with
    | some unit => resolveUnit .sendWorker unit d.sendWorkQueue
    | none => pure headPid
  return (named, pid)

/-- Original queue erase, pending test and pending clear. -/
def sendWorkerDequeue (pid : PeerId) : M Unit := do
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue.erase pid }
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid { p with handshakePending := false }

theorem runOneSendWorker_source :
    Env.runOneSendWorker = (do
      let selected ← sendWorkerSelection
      sendWorkerDequeue selected.2
      Env.runWorker .sendWorker (handshakeSendWorker selected.2)) := by
  simp only [Env.runOneSendWorker, sendWorkerSelection, sendWorkerDequeue, bind_assoc, pure_bind]
  congr 1
  funext d
  cases h : d.sendWorkQueue.head? with
  | none => simp only [h, invariant, throw_bind_timer]
  | some headPid =>
    simp only [h, bind_assoc, pure_bind]
    congr 1
    funext named
    cases named with
    | none =>
      simp only [bind_assoc, pure_bind]
      congr 1
      funext u
      congr 1
      funext p
      split <;> simp only [bind_assoc]
    | some unit =>
      simp only [bind_assoc, pure_bind]
      congr 1
      funext pid
      congr 1
      funext u
      congr 1
      funext p
      split <;> simp only [bind_assoc]

/-- Normal selection records the exact named/head rule and leaves the lookup stores unchanged. -/
theorem sendWorkerSelection_effect (d : Device) (units : List (Nat × Nat × Nat)) :
    Ensures sendWorkerSelection (fun w => w.k.wg = some d ∧ w.unitPeers = units)
      (fun selected w => w.k.wg = some d ∧ w.unitPeers = units ∧
        SendSelectionMatches d units selected.1 selected.2) := by
  have hp := peekUnit_dispatch_frame (fun k us => k.wg = some d ∧ us = units)
  rw [ensures_iff]
  mvcgen [sendWorkerSelection, getDev, getK, resolveUnit, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [SendSelectionMatches]
  all_goals grind [List.mem_of_head?]

/-- The successful pending test is a conclusion; it is not an input invariant. -/
theorem sendWorkerDequeue_effect (pid : PeerId) (d : Device) :
    Ensures (sendWorkerDequeue pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ p, d.peers[pid]? = some p ∧ p.handshakePending = true ∧
        w.k.wg = some (dequeuedSendDevice d pid p)) := by
  rw [ensures_iff]
  mvcgen [sendWorkerDequeue, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [dequeuedSendDevice]
  all_goals grind

/-- Pure snapshot reads decorate the original selection, dequeue and section sequence. -/
def sendWorkerExecution : M SendWorkerExecution := do
  let selected ← sendWorkerSelection
  sendWorkerDequeue selected.2
  let beforeSection ← Campaign2.read
  let startBytes ← hidden (.sectionStart .sendWorker)
  let afterStart ← Campaign2.read
  handshakeSendWorker selected.2
  let afterBody ← Campaign2.read
  let stopBytes ← hidden (.sectionStop .sendWorker)
  return ⟨selected.1, selected.2, beforeSection, startBytes, afterStart, afterBody, stopBytes⟩

theorem sendWorkerSection_source (body : M Unit) :
    Env.runWorker .sendWorker body = (do
      let _ ← hidden (.sectionStart .sendWorker)
      body
      let _ ← hidden (.sectionStop .sendWorker)
      pure ()) := by rfl

/-- Erasure is exact, including all prefix, body and section-read errors. -/
theorem sendWorkerExecution_erase :
    (do let _ ← sendWorkerExecution; pure ()) = Env.runOneSendWorker := by
  rw [runOneSendWorker_source]
  funext w
  change StateT.run _ w = StateT.run _ w
  simp only [sendWorkerExecution, sendWorkerSection_source, StateT.run_bind, Campaign2.read, StateT.run_pure]
  cases hs : sendWorkerSelection.run w with
  | error e => rfl
  | ok pair =>
    obtain ⟨selected, afterSelection⟩ := pair
    dsimp only [Bind.bind, Except.bind, Pure.pure]
    cases hd : (sendWorkerDequeue selected.2).run afterSelection with
    | error e => rfl
    | ok pair =>
      obtain ⟨u, beforeSection⟩ := pair
      cases u
      dsimp only [Bind.bind, Except.bind, Pure.pure, Campaign2.read, StateT.run, get]
      cases hb : hidden (.sectionStart .sendWorker) beforeSection with
      | error e => rfl
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        try dsimp only [Bind.bind, Except.bind, Pure.pure, Campaign2.read, StateT.run, get]
        cases hw : handshakeSendWorker selected.2 afterStart with
        | error e => rfl
        | ok pair =>
          obtain ⟨u, afterBody⟩ := pair
          cases u
          try dsimp only [Bind.bind, Except.bind, Pure.pure, Campaign2.read, StateT.run, get]
          cases he : hidden (.sectionStop .sendWorker) afterBody <;> rfl

theorem sendWorkerExecution_effect (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Ensures sendWorkerExecution
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (CompletedSendWorker d units) := by
  intro w execution final pre run
  change (sendWorkerSelection.run w >>= fun sel =>
    (sendWorkerDequeue sel.1.2).run sel.2 >>= fun deq =>
    (hidden (.sectionStart .sendWorker)).run deq.2 >>= fun start =>
    (handshakeSendWorker sel.1.2).run start.2 >>= fun body =>
    (hidden (.sectionStop .sendWorker)).run body.2 >>= fun stop =>
    Except.ok (SendWorkerExecution.mk sel.1.1 sel.1.2 (Campaign2.snapshot deq.2)
      start.1 (Campaign2.snapshot start.2) (Campaign2.snapshot body.2) stop.1, stop.2)) =
      .ok (execution, final) at run
  cases hs : sendWorkerSelection.run w with
  | error e => simp only [hs, Bind.bind, Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨selected, afterSelection⟩ := pair
    simp only [hs, Bind.bind, Except.bind] at run
    cases hd : (sendWorkerDequeue selected.2).run afterSelection with
    | error e => simp only [hd] at run; cases run
    | ok pair =>
      obtain ⟨u, beforeSection⟩ := pair
      simp only [hd] at run
      cases hb : (hidden (.sectionStart .sendWorker)).run beforeSection with
      | error e => simp only [hb] at run; cases run
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        simp only [hb] at run
        cases hw : (handshakeSendWorker selected.2).run afterStart with
        | error e => simp only [hw] at run; cases run
        | ok pair =>
          obtain ⟨u, afterBody⟩ := pair
          simp only [hw] at run
          cases he : (hidden (.sectionStop .sendWorker)).run afterBody with
          | error e => simp only [he] at run; cases run
          | ok pair =>
            obtain ⟨stopBytes, afterStop⟩ := pair
            simp only [he] at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
            have selection := sendWorkerSelection_effect d units w selected afterSelection pre hs
            obtain ⟨p, resident, pending, deq⟩ :=
              sendWorkerDequeue_effect selected.2 d afterSelection _ beforeSection selection.1 hd
            have start := (ensures_iff _ _ _).mpr
              (hidden_kernel_spec (fun k => k.wg = some (dequeuedSendDevice d selected.2 p))
                (.sectionStart .sendWorker)) beforeSection bytes afterStart deq hb
            have workerPre : workerAt afterStart selected.2 =
                some (p.internalId, p.timerHandshakeAttempts, p.refcount) := by
              simp [workerAt, peerAt, start, dequeuedSendDevice, workerView]
            have body := handshakeSendWorker_workerView selected.2 p.internalId
              p.timerHandshakeAttempts p.refcount
              (retained selected.2 selection.2.2.1 p resident)
              afterStart _ afterBody workerPre hw
            have stop := (ensures_iff _ _ _).mpr
              (hidden_kernel_spec
                (fun k => ((k.wg.bind fun d => d.peers[selected.2]?).map workerView) =
                  some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1))
                (.sectionStop .sendWorker)) afterBody stopBytes afterStop body he
            exact ⟨selection.2.2, p, resident, pending, deq, start, body, stop⟩

/-- Every successful original call has a coherent decorated execution. -/
theorem sendWorkerExecution_success (w final : World)
    (run : Env.runOneSendWorker.run w = .ok ((), final)) :
    ∃ execution, sendWorkerExecution.run w = .ok (execution, final) := by
  have erased : (do let _ ← sendWorkerExecution; pure () : M Unit).run w = .ok ((), final) := by
    rw [sendWorkerExecution_erase]
    exact run
  change (sendWorkerExecution.run w >>= fun out => Except.ok ((), out.2)) =
    .ok ((), final) at erased
  cases he : sendWorkerExecution.run w with
  | error e => simp only [he, Bind.bind, Except.bind] at erased; cases erased
  | ok pair =>
    obtain ⟨execution, after⟩ := pair
    simp only [he, Bind.bind, Except.bind] at erased
    have eq := congrArg Prod.snd (Except.ok.inj erased)
    cases eq
    exact ⟨execution, rfl⟩

end Leanux.Proofs.WG.TimerDiscipline
