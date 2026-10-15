import Leanux.Proofs.WG.TimerDiscipline.FireReadyFrames
import Leanux.Proofs.WG.TimerDiscipline.FireSelectionSource
import Leanux.Proofs.WG.TimerDiscipline.RetryReadySource

/-! Total original selection, timer removal, section consumption and callback composition. The final ready-run theorem derives callback success from static guards and supplied records. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline

theorem peek_start (w : World) (bytes : List UInt8) (rest : List HiddenRecord)
    (present : w.hidden = some (sectionRecord true bytes :: rest))
    (size : bytes.length = 16) (nonzero : recordWordOf bytes 1 ≠ 0) :
    (peekUnit .timerRetransmit).run w = .ok (some (recordWordOf bytes 1),w) := by
  have unchanged : {w with hidden := some (sectionRecord true bytes :: rest)} = w := by
    rw [← present]
  simp only [peekUnit, skipAmbient, StateT.run, bind, pure, get, getThe, MonadStateOf.get,
    set, StateT.bind, StateT.pure, StateT.get, StateT.set, Except.bind, Except.pure,
    present, section_drop]
  simp [sectionRecord, sectionSite, size, nonzero, StateT.pure, pure, Except.pure]
  exact unchanged

theorem selection (w : World) (d : Device) (horizon : UInt64) (pid : PeerId)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (device : w.k.wg = some d)
    (present : w.hidden = some (sectionRecord true bytes :: rest))
    (size : bytes.length = 16) (nonzero : recordWordOf bytes 1 ≠ 0)
    (registered : w.timerUnits.find? (·.1 == recordWordOf bytes 1) =
      some (recordWordOf bytes 1, pid, .retransmitHandshake))
    (due : pid ∈ duePeers d .retransmitHandshake horizon) :
    (timerSelection .timerRetransmit horizon).run w = .ok ((pid,.retransmitHandshake),w) := by
  have peek := peek_start w bytes rest present size nonzero
  have getDevice : getDev.run w = .ok (d,w) := by
    simp [getDev, getK, StateT.run, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.pure, StateT.get, Except.bind, Except.pure, device]
  simp only [timerSelection, Worker.timer?, StateT.run_bind, getDevice]
  simp only [bind, Except.bind, StateT.run_bind, peek, StateT.run_get]
  have sameTimer : (PeerTimer.retransmitHandshake != PeerTimer.retransmitHandshake) = false := rfl
  have due' := List.mem_filter.mp due
  simp [StateT.run, bind, pure, get, getThe, MonadStateOf.get, StateT.bind,
    StateT.pure, StateT.get, Except.bind, Except.pure, registered, sameTimer, due'.1]
  obtain ⟨_, p, expiry, resident, armed, earlier⟩ := duePeer_resident d .retransmitHandshake horizon pid due
  simp [resident, armed, earlier]
  rfl

theorem section_read (start : Bool) (w : World) (bytes : List UInt8)
    (rest : List HiddenRecord)
    (present : w.hidden = some (sectionRecord start bytes :: rest))
    (size : bytes.length = if start then 16 else 8) :
    (hidden (sectionSite start)).run w = .ok (bytes,{w with
      hidden := some rest
      pendingWork := if start then w.pendingWork.filter (· != Worker.timerRetransmit.index) else w.pendingWork}) := by
  simp only [hidden, skipAmbient, StateT.run, bind, pure, get, getThe,
    MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    Except.bind, Except.pure, present, section_drop]
  cases start <;>
    simp [noteNetRxStart, sectionRecord, sectionSite, HiddenSite.info, Worker.sectionId,
      Worker.index, size, StateT.bind, StateT.pure, StateT.set, pure, bind, Except.bind, Except.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      List.take_of_length_le (by simpa using Nat.le_of_eq size),
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_eq size)]

theorem detach (w : World) (d : Device) (p : Peer) (pid : PeerId)
    (device : w.k.wg = some d) (resident : d.peers[pid]? = some p) :
    (delTimer pid .retransmitHandshake).run w = .ok ((), afterDetach w d p pid) := by
  simp [delTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    StateT.run, bind, pure, get, getThe, MonadStateOf.get, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    Except.bind, Except.pure, device, resident, afterDetach]

theorem section_total (body : M Unit) (w after : World)
    (start stop : List UInt8) (rest suffix : List HiddenRecord)
    (present : w.hidden = some (sectionRecord true start :: rest))
    (startSize : start.length = 16) (stopSize : stop.length = 8)
    (callback : body.run (sectionEntry w rest) = .ok ((),after))
    (ended : after.hidden = some (sectionRecord false stop :: suffix)) :
    (runTimerSection .timerRetransmit body).run w =
      .ok ((),{after with hidden := some suffix}) := by
  have beginRead := section_read true
    {w with fired := w.fired.push Worker.timerRetransmit.symbol} start rest present startSize
  have endRead := section_read false after stop suffix ended stopSize
  simp only [sectionSite, ite_true, Bool.false_eq_true, ite_false] at beginRead endRead
  simp only [runTimerSection, Worker.timer?, Option.isNone_some, Bool.false_eq_true, ite_false]
  change ((do
    modify fun (s : World) => {s with fired := s.fired.push Worker.timerRetransmit.symbol}
    let _ ← hidden (.sectionStart .timerRetransmit)
    body
    let _ ← hidden (.sectionStop .timerRetransmit)
    pure ()).run w) = _
  simp only [StateT.run_bind]
  change ((do let _ ← hidden (.sectionStart .timerRetransmit)
              body
              let _ ← hidden (.sectionStop .timerRetransmit)
              pure ()).run {w with fired := w.fired.push Worker.timerRetransmit.symbol}) = _
  rw [StateT.run_bind, beginRead]
  change ((do body
              let _ ← hidden (.sectionStop .timerRetransmit)
              pure ()).run (sectionEntry w rest)) = _
  rw [StateT.run_bind, callback]
  change ((do let _ ← hidden (.sectionStop .timerRetransmit); pure ()).run after) = _
  rw [StateT.run_bind, endRead]
  rfl

theorem fire_total (w after : World) (d : Device) (p : Peer) (pid : PeerId)
    (horizon : UInt64) (start stop : List UInt8) (rest suffix : List HiddenRecord)
    (device : w.k.wg = some d) (resident : d.peers[pid]? = some p)
    (present : w.hidden = some (sectionRecord true start :: rest))
    (startSize : start.length = 16) (stopSize : stop.length = 8)
    (nonzero : recordWordOf start 1 ≠ 0)
    (registered : w.timerUnits.find? (·.1 == recordWordOf start 1) =
      some (recordWordOf start 1,pid,.retransmitHandshake))
    (due : pid ∈ duePeers d .retransmitHandshake horizon)
    (callback : (expiredRetransmitHandshake pid).run
      (sectionEntry (afterDetach w d p pid) rest) = .ok ((),after))
    (ended : after.hidden = some (sectionRecord false stop :: suffix)) :
    (fireTimer .timerRetransmit horizon).run w = .ok ((),{after with hidden := some suffix}) := by
  have selected := selection w d horizon pid start rest device present startSize nonzero registered due
  rw [fireTimer_source, StateT.run_bind, selected]
  change (fireSelected .timerRetransmit pid .retransmitHandshake).run w = _
  simp only [fireSelected, StateT.run_bind]
  rw [detach w d p pid device resident]
  change (runTimerSection .timerRetransmit (expiredRetransmitHandshake pid)).run (afterDetach w d p pid) = _
  exact section_total (expiredRetransmitHandshake pid) (afterDetach w d p pid) after
    start stop rest suffix present startSize stopSize callback ended

theorem fire_ready_run (w : World) (d : Device) (p : Peer) (pid : PeerId) (horizon : UInt64)
    (start cache clock queue stop : List UInt8) (suffix : List HiddenRecord)
    (device : w.k.wg = some d) (resident : d.peers[pid]? = some p)
    (due : pid ∈ duePeers d .retransmitHandshake horizon)
    (startLen : start.length=16) (stopLen : stop.length=8)
    (cacheLen : cache.length=8) (clockLen : clock.length=8) (queueLen : queue.length=16)
    (nonzero : recordWordOf start 1 ≠ 0)
    (registered : w.timerUnits.find? (·.1 == recordWordOf start 1) =
      some (recordWordOf start 1,pid,.retransmitHandshake))
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES)
    (alive : p.isDead=false) (pending : p.handshakePending=false)
    (positive : 0<p.refcount) (bounded : p.refcount+1<2^31)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64*NSEC_PER_SEC64 ≤ (RetryReady.word clock).toInt64)
    (mode : w.armRecords=true) (cacheMode : w.dstCacheRecords=true)
    (unit : w.unitPeers.find? (fun e => e.2.1 == Worker.sendWorker.index && e.2.2 == pid) =
      some (recordWordOf queue 0,Worker.sendWorker.index,pid))
    (records : w.hidden = some (suppliedRecords start cache clock queue stop suffix)) :
    (fireTimer .timerRetransmit horizon).run w = .ok ((),fireResult w d p pid cache clock suffix) := by
  let rest := {site:=150,bytes:=cache}::{site:=6,bytes:=clock}::
    {site:=(HiddenSite.queued .sendWorker).info.id,bytes:=queue}::sectionRecord false stop::suffix
  have afterResident : (detachedDevice d p pid).peers[pid]? =
      some (p.setTimer .retransmitHandshake none) := by
    simp [detachedDevice]
  have callback := RetryReady.callback_run pid (detachedDevice d p pid)
    (p.setTimer .retransmitHandshake none) cache clock queue (sectionRecord false stop::suffix)
    (sectionEntry (afterDetach w d p pid) rest)
    afterResident rfl limit alive pending positive bounded expired cacheLen clockLen queueLen
    mode cacheMode unit rfl
  have fired := fire_total w _ d p pid horizon start stop rest suffix device resident
    records startLen stopLen nonzero registered due callback rfl
  simpa [fireResult, sectionEntry, afterDetach] using fired

end Leanux.Proofs.WG.TimerDiscipline.FireReady
