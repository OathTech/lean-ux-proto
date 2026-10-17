import Leanux.Proofs.WG.TimerDiscipline.SendDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchFrames
import Leanux.Proofs.WG.TimerDiscipline.SendWorkerSource
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Env

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000


namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Original head/named selection, before the dequeue. -/
def sendWorkerSelection : Leanux.M (Option Nat × PeerId) := do
  let d ← getDev
  let some headPid := d.sendWorkQueue.head? | invariant "no queued handshake send work"
  let named ← peekUnit .sendWorker
  let pid ← match named with
    | some unit => resolveUnit .sendWorker unit d.sendWorkQueue
    | none => pure headPid
  return (named, pid)

/-- Actual queue erase, pending test and residual-queue pending update. -/
def sendWorkerDequeue (pid : PeerId) : Leanux.M Unit := do
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue.erase pid }
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid { p with handshakePending := (← getDev).sendWorkQueue.contains pid }

theorem runOneSendWorker_source :
    Env.runOneSendWorker = (do
      let selected ← sendWorkerSelection
      sendWorkerDequeue selected.2
      Env.runWorker .sendWorker (handshakeSendWorker selected.2)) := by
  simp only [Env.runOneSendWorker, sendWorkerSelection, sendWorkerDequeue, bind_assoc, pure_bind]
  congr 1
  funext d
  cases h : d.sendWorkQueue.head? with
  | none => rfl
  | some headPid =>
    simp only [bind_assoc]
    congr 1
    funext named
    cases named with
    | none =>
      simp only [pure_bind]
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
    Product.Ensures sendWorkerSelection (fun w => w.wg.dev = some d ∧ w.ambient.unitPeers = units)
      (fun selected w => w.wg.dev = some d ∧ w.ambient.unitPeers = units ∧
        SendSelectionMatches d units selected.1 selected.2) := by
  intro w result final pre run
  have read : (liftWG getDev).run w = .ok (d, w) := by
    change (((getDev).run w.wg).run w.ambient >>= fun ((value, g), a) =>
      Except.ok (value, {w with wg := g, ambient := a})) = _
    simp [getDev, pre.1]
  change ((liftWG getDev).run w >>= _) = _ at run
  rw [read] at run
  dsimp only [Bind.bind, Except.bind] at run
  cases head : d.sendWorkQueue.head? with
  | none =>
    simp only [head] at run
    change (Except.error (.invariant "no queued handshake send work") : Except Stop _) = _ at run
    cases run
  | some headPid =>
    simp only [head] at run
    change ((peekUnit .sendWorker : Leanux.M (Option Nat)).run w >>= _) = _ at run
    cases peek : (peekUnit .sendWorker : Leanux.M (Option Nat)).run w with
    | error stop => rw [peek] at run; cases run
    | ok pair =>
      obtain ⟨named, current⟩ := pair
      have frame := peekUnit_dispatch_frame (fun g _ _ _ us => g.dev = some d ∧ us = units)
        w named current pre peek
      rw [peek] at run
      dsimp only [Bind.bind, Except.bind] at run
      cases named with
      | none =>
        cases run
        exact ⟨frame.1, frame.2, List.mem_of_head? head, head⟩
      | some unit =>
        have resolved (initial : World) (value : Nat) (finish : World)
            (sameUnits : initial.ambient.unitPeers = units)
            (actual : (resolveUnit .sendWorker unit d.sendWorkQueue : Leanux.M Nat).run initial =
              .ok (value, finish)) :
            finish = initial ∧ SendSelectionMatches d units (some unit) value := by
          change ((AmbientM.resolveUnit .sendWorker unit d.sendWorkQueue).run initial.ambient >>=
            fun (pid, after) => Except.ok (pid, {initial with ambient := after})) = _ at actual
          have resolver : (AmbientM.resolveUnit .sendWorker unit d.sendWorkQueue).run initial.ambient =
              match units.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) with
              | none => .error (.hidden s!"{Worker.sendWorker.symbol}: the dispatched unit {unit} was never queued")
              | some (_, _, pid) => if !d.sendWorkQueue.contains pid then
                  .error (.hidden s!"{Worker.sendWorker.symbol}: the dispatched unit is peer {pid}'s, which is not queued")
                else .ok (pid, initial.ambient) := by
            simp only [AmbientM.resolveUnit, StateT.run_bind, StateT.run_get, pure_bind, sameUnits]
            cases found : units.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) with
            | none => rfl
            | some entry =>
              obtain ⟨address, worker, pid⟩ := entry
              by_cases member : pid ∈ d.sendWorkQueue <;> simp [member]
              all_goals rfl
          rw [resolver] at actual
          cases found : units.find? (fun e => e.1 == unit && e.2.1 == Worker.sendWorker.index) with
          | none => rw [found] at actual; cases actual
          | some entry =>
            obtain ⟨address, worker, pid⟩ := entry
            rw [found] at actual
            by_cases member : pid ∈ d.sendWorkQueue
            · simp [member] at actual
              rcases actual with ⟨rfl, rfl⟩
              exact ⟨rfl, member, ⟨(address, worker, pid), found, rfl⟩⟩
            · simp [member] at actual
              cases actual
        change ((resolveUnit .sendWorker unit d.sendWorkQueue : Leanux.M Nat).run current >>=
          fun (pid, after) => Except.ok ((some unit, pid), after)) = _ at run
        cases actual : (resolveUnit .sendWorker unit d.sendWorkQueue : Leanux.M Nat).run current with
        | error stop => rw [actual] at run; cases run
        | ok out =>
          obtain ⟨pid, after⟩ := out
          obtain ⟨same, selection⟩ := resolved current pid after frame.2 actual
          subst after
          rw [actual] at run
          cases run
          exact ⟨frame.1, frame.2, selection⟩

/-- A normal pending test yields residency and the original true flag without an input invariant. -/
theorem sendWorkerDequeue_effect (pid : PeerId) (d : Device) :
    Product.Ensures (sendWorkerDequeue pid) (fun w => w.wg.dev = some d)
      (fun _ w => ∃ p, d.peers[pid]? = some p ∧ p.handshakePending = true ∧
        w.wg.dev = some (dequeuedSendDevice d pid p)) := by
  intro w result final pre run
  let next : World := {w with wg := {w.wg with dev := some {d with sendWorkQueue := d.sendWorkQueue.erase pid}}}
  have modifyRun : (liftM (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) : Leanux.M Unit).run w =
      .ok ((), next) := by
    change Except.ok ((), {w with wg := {w.wg with dev := w.wg.dev.map _}}) = _
    rw [pre]
    rfl
  unfold sendWorkerDequeue at run
  simp only [StateT.run_bind] at run
  change ((liftM (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) : Leanux.M Unit).run w >>= _) = _ at run
  rw [modifyRun] at run
  change ((liftM (getPeer pid) : Leanux.M Peer).run next >>= _) = _ at run
  cases resident : d.peers[pid]? with
  | none =>
    have missing : (liftM (getPeer pid) : Leanux.M Peer).run next = .error (.invariant s!"dangling peer {pid}") := by
      change (((getPeer pid).run next.wg).run next.ambient >>= _) = _
      simp [getPeer, getDev, next, resident, invariant, AmbientM.invariant]
      rfl
    rw [missing] at run
    cases run
  | some p =>
    have read : (liftM (getPeer pid) : Leanux.M Peer).run next = .ok (p, next) := by
      change (((getPeer pid).run next.wg).run next.ambient >>= _) = _
      simp [getPeer, getDev, next, resident]
      rfl
    rw [read] at run
    dsimp only [Bind.bind, Except.bind] at run
    cases pending : p.handshakePending with
    | false =>
      rw [pending] at run
      change (Except.error (.invariant "queued work without a pending flag") : Except Stop _) = _ at run
      cases run
    | true =>
      rw [pending] at run
      change ((liftM getDev : Leanux.M Device).run next >>= _) = _ at run
      have readDev : (liftM getDev : Leanux.M Device).run next = .ok ({d with sendWorkQueue := d.sendWorkQueue.erase pid}, next) := by
        rfl
      rw [readDev] at run
      change Except.ok ((), {w with wg := {w.wg with dev := some (dequeuedSendDevice d pid p)}}) = _ at run
      cases run
      exact ⟨p, rfl, pending, rfl⟩

/-- Pure snapshot reads decorate the original selection, dequeue and section sequence. -/
def sendWorkerExecution : Leanux.M SendWorkerExecution := do
  let selected ← sendWorkerSelection
  sendWorkerDequeue selected.2
  let beforeSection ← Campaign2.Product.read
  let startBytes ← hidden (.sectionStart .sendWorker)
  let afterStart ← Campaign2.Product.read
  handshakeSendWorker selected.2
  let afterBody ← Campaign2.Product.read
  let stopBytes ← hidden (.sectionStop .sendWorker)
  return ⟨selected.1, selected.2, beforeSection, startBytes, afterStart, afterBody, stopBytes⟩

theorem sendWorkerSection_source (body : Leanux.M Unit) :
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
  simp only [sendWorkerExecution, sendWorkerSection_source, StateT.run_bind, StateT.run_pure]
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
      dsimp only [Bind.bind, Except.bind, Pure.pure, Campaign2.Product.read, StateT.run, get]
      cases hb : (hidden (.sectionStart .sendWorker) : Leanux.M (List UInt8)) beforeSection with
      | error e => rfl
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        try dsimp only [Bind.bind, Except.bind, Pure.pure, Campaign2.Product.read, StateT.run, get]
        cases hw : (liftM (handshakeSendWorker selected.2) : Leanux.M Unit) afterStart with
        | error e => rfl
        | ok pair =>
          obtain ⟨u, afterBody⟩ := pair
          cases u
          try dsimp only [Bind.bind, Except.bind, Pure.pure, Campaign2.Product.read, StateT.run, get]
          cases he : (hidden (.sectionStop .sendWorker) : Leanux.M (List UInt8)) afterBody <;> rfl

theorem sendWorkerExecution_effect (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Product.Ensures sendWorkerExecution
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (CompletedSendWorker d units) := by
  intro w execution final pre run
  change (sendWorkerSelection.run w >>= fun sel =>
    (sendWorkerDequeue sel.1.2).run sel.2 >>= fun deq =>
    (hidden (.sectionStart .sendWorker) : Leanux.M (List UInt8)).run deq.2 >>= fun start =>
    (liftWG (handshakeSendWorker sel.1.2)).run start.2 >>= fun body =>
    (hidden (.sectionStop .sendWorker) : Leanux.M (List UInt8)).run body.2 >>= fun stop =>
    Except.ok (SendWorkerExecution.mk sel.1.1 sel.1.2 (Campaign2.Product.snapshot deq.2)
      start.1 (Campaign2.Product.snapshot start.2) (Campaign2.Product.snapshot body.2) stop.1, stop.2)) =
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
      cases hb : (hidden (.sectionStart .sendWorker) : Leanux.M (List UInt8)).run beforeSection with
      | error e => simp only [hb] at run; cases run
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        simp only [hb] at run
        cases hw : (liftWG (handshakeSendWorker selected.2)).run afterStart with
        | error e => simp only [hw] at run; cases run
        | ok pair =>
          obtain ⟨u, afterBody⟩ := pair
          simp only [hw] at run
          cases he : (hidden (.sectionStop .sendWorker) : Leanux.M (List UInt8)).run afterBody with
          | error e => simp only [he] at run; cases run
          | ok pair =>
            obtain ⟨stopBytes, afterStop⟩ := pair
            simp only [he] at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
            have selection := sendWorkerSelection_effect d units w selected afterSelection pre hs
            obtain ⟨p, resident, pending, deq⟩ :=
              sendWorkerDequeue_effect selected.2 d afterSelection _ beforeSection selection.1 hd
            have ambientFrame {α : Type} (action : AmbientM α) (P : WGWorld → Prop) :
                Product.Ensures (liftAmbient action) (fun w => P w.wg) (fun _ w => P w.wg) := by
              intro initial value finish property actionRun
              change (action.run initial.ambient >>= fun (a, ambient) =>
                Except.ok (a, {initial with ambient})) = .ok (value, finish) at actionRun
              cases h : action.run initial.ambient with
              | error stop => rw [h] at actionRun; cases actionRun
              | ok pair => rw [h] at actionRun; cases actionRun; exact property
            have start := ambientFrame (AmbientM.hidden (.sectionStart .sendWorker))
              (fun g => g.dev = some (dequeuedSendDevice d selected.2 p))
              beforeSection bytes afterStart deq hb
            have workerPre : workerAt afterStart.wg selected.2 =
                some (p.internalId, p.timerHandshakeAttempts, p.refcount) := by
              simp [workerAt, peerAt, start, dequeuedSendDevice, workerView]
            have body : workerAt afterBody.wg selected.2 =
                some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1) := by
              change (((handshakeSendWorker selected.2).run afterStart.wg).run afterStart.ambient >>=
                fun ((value, g), ambient) => Except.ok (value, {afterStart with wg := g, ambient})) = _ at hw
              cases actual : ((handshakeSendWorker selected.2).run afterStart.wg).run afterStart.ambient with
              | error stop => rw [actual] at hw; cases hw
              | ok pair =>
                obtain ⟨⟨value, g⟩, ambient⟩ := pair
                rw [actual] at hw
                cases hw
                exact handshakeSendWorker_workerView selected.2 p.internalId
                  p.timerHandshakeAttempts p.refcount
                  (retained selected.2 selection.2.2.1 p resident)
                  afterStart.wg afterStart.ambient u g ambient workerPre actual
            have stop := ambientFrame (AmbientM.hidden (.sectionStop .sendWorker))
              (fun g => workerAt g selected.2 =
                some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1))
              afterBody stopBytes afterStop body he
            exact ⟨selection.2.2, p, resident, pending, deq, start, body, stop⟩

/-- Every successful original call has a coherent decorated execution. -/
theorem sendWorkerExecution_success (w final : World)
    (run : Env.runOneSendWorker.run w = .ok ((), final)) :
    ∃ execution, sendWorkerExecution.run w = .ok (execution, final) := by
  have erased : (do let _ ← sendWorkerExecution; pure () : Leanux.M Unit).run w = .ok ((), final) := by
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
