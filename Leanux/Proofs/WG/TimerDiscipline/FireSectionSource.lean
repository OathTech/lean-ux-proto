import Leanux.Proofs.WG.TimerDiscipline.FireSectionModel
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline

theorem peek_start (w : World) (bytes : List UInt8) (rest : List HiddenRecord)
    (present : w.ambient.hidden = some (sectionRecord true bytes :: rest))
    (size : bytes.length = 16) (nonzero : recordWordOf bytes 1 ≠ 0) :
    (peekUnit .timerRetransmit : Leanux.M _).run w = .ok (some (recordWordOf bytes 1),w) := by
  have ambientProduct {α : Type} (action : AmbientM α) :
      (monadLift action : Leanux.M α) = liftAmbient action := rfl
  have passive : HiddenSite.passive 102 = false := rfl
  simp [passive, ambientProduct, liftAmbient, peekUnit, AmbientM.peekUnit, AmbientM.skipAmbient,
    present, sectionRecord, sectionSite, HiddenSite.info, Worker.sectionId, Worker.index, size, nonzero,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set,
    StateT.bind, StateT.pure, StateT.get, StateT.set, Except.bind, Except.pure]
  change {w with ambient := {w.ambient with hidden := some (sectionRecord true bytes :: rest)}} = w
  rw [←present]

theorem section_read (start : Bool) (w : World) (bytes : List UInt8)
    (rest : List HiddenRecord)
    (present : w.ambient.hidden = some (sectionRecord start bytes :: rest))
    (size : bytes.length = if start then 16 else 8) :
    (hidden (sectionSite start) : Leanux.M _).run w = .ok (bytes,{w with
      ambient := {w.ambient with
        hidden := some rest
        pendingWork := if start then w.ambient.pendingWork.filter (· != Worker.timerRetransmit.index)
          else w.ambient.pendingWork}}) := by
  have ambientProduct {α : Type} (action : AmbientM α) :
      (monadLift action : Leanux.M α) = liftAmbient action := rfl
  have passiveStart : HiddenSite.passive 102 = false := rfl
  have passiveStop : HiddenSite.passive 103 = false := rfl
  cases start <;>
    simp [passiveStart, passiveStop, ambientProduct, liftAmbient, hidden, AmbientM.hidden, AmbientM.skipAmbient,
      AmbientM.noteNetRxStart, present, sectionRecord, sectionSite,
      HiddenSite.info, Worker.sectionId, Worker.index, size,
      List.take_of_length_le (by simpa using Nat.le_of_eq size),
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_eq size),
      StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, set, modify, modifyGet,
      StateT.bind, StateT.pure, StateT.get, StateT.set, MonadStateOf.modifyGet,
      StateT.modifyGet, Except.bind, Except.pure]

theorem detach (w : World) (d : Device) (p : Peer) (pid : PeerId)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p) :
    (liftWG (delTimer pid .retransmitHandshake)).run w = .ok ((), afterDetach w d p pid) := by
  simp [liftWG, delTimer, getPeer, getDev, setPeer, modifyDev,
    StateT.run, Bind.bind, Pure.pure, get, getThe, MonadStateOf.get, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    Except.bind, Except.pure, device, resident, afterDetach, detachedDevice, detachedPeer]

theorem section_total (body : Leanux.M Unit) (w after : World)
    (start stop : List UInt8) (rest suffix : List HiddenRecord)
    (present : w.ambient.hidden = some (sectionRecord true start :: rest))
    (startSize : start.length = 16) (stopSize : stop.length = 8)
    (callback : body.run (sectionEntry w rest) = .ok ((),after))
    (ended : after.ambient.hidden = some (sectionRecord false stop :: suffix)) :
    (runTimerSection .timerRetransmit body).run w =
      .ok ((),{after with ambient := {after.ambient with hidden := some suffix}}) := by
  have beginRead := section_read true
    {w with ambient := {w.ambient with fired := w.ambient.fired.push Worker.timerRetransmit.symbol}}
    start rest present startSize
  have endRead := section_read false after stop suffix ended stopSize
  simp only [sectionSite, ite_true, Bool.false_eq_true, ite_false] at beginRead endRead
  have factor : runTimerSection .timerRetransmit body = (do
      modifyAmbient fun s => {s with fired := s.fired.push Worker.timerRetransmit.symbol}
      let _ ← hidden (.sectionStart .timerRetransmit)
      body
      let _ ← hidden (.sectionStop .timerRetransmit)
      pure ()) := by
    simp only [runTimerSection, runWorker, Worker.timer?, Option.isNone_some,
      Bool.false_eq_true, ite_false]
    rfl
  rw [factor]
  simp only [StateT.run_bind]
  change ((do let _ ← hidden (.sectionStart .timerRetransmit)
              body
              let _ ← hidden (.sectionStop .timerRetransmit)
              pure ()).run
      {w with ambient := {w.ambient with fired := w.ambient.fired.push Worker.timerRetransmit.symbol}}) = _
  rw [StateT.run_bind, beginRead]
  change ((do body
              let _ ← hidden (.sectionStop .timerRetransmit)
              pure ()).run (sectionEntry w rest)) = _
  rw [StateT.run_bind, callback]
  change ((do let _ ← hidden (.sectionStop .timerRetransmit); pure () : Leanux.M Unit).run after) = _
  rw [StateT.run_bind, endRead]
  rfl
end Leanux.Proofs.WG.TimerDiscipline.FireReady
