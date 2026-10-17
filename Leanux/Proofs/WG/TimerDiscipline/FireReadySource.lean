import Leanux.Proofs.WG.TimerDiscipline.FireReadyFrames
import Leanux.Proofs.WG.TimerDiscipline.FireSectionSource
import Leanux.Proofs.WG.TimerDiscipline.FireUnitSource
import Leanux.Proofs.WG.TimerDiscipline.RetryReadySource

/-! Exact selected-unit execution on the original supplied-record domain. The historical logical-due premise is retained but does not prove outer wheel selection. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline
theorem selection (w : World) (d : Device) (horizon : UInt64) (pid : PeerId)
    (we : WheelEntry) (bytes : List UInt8) (rest : List HiddenRecord)
    (_device : w.wg.dev = some d)
    (present : w.ambient.hidden = some (sectionRecord true bytes :: rest))
    (size : bytes.length = 16) (nonzero : recordWordOf bytes 1 ≠ 0)
    (registered : w.wg.timerUnits.find? (·.1 == recordWordOf bytes 1) =
      some (recordWordOf bytes 1, pid, .retransmitHandshake))
    (_due : pid ∈ duePeers d .retransmitHandshake horizon) :
    (timerDispatchPrefix_variant .timerRetransmit pid .retransmitHandshake we none).run w =
      .ok ((),w) := by
  have worker : timerWorker .retransmitHandshake = pure Worker.timerRetransmit := rfl
  have peek := peek_start w bytes rest present size nonzero
  simp only [timerDispatchPrefix_variant, worker, pure_bind]
  change ((do
    if let some u ← (peekUnit .timerRetransmit : Leanux.M _) then
      match (← (getWG : Leanux.M WGWorld)).timerUnits.find? (·.1 == u) with
      | some (_, pid', t') =>
        if pid' != pid || t' != .retransmitHandshake then
          throw (.hidden s!"the wheel runs peer {pid}'s {repr PeerTimer.retransmitHandshake} timer next; the section names peer {pid'}'s {repr t'}")
      | none => throw (.hidden s!"a section of {Worker.timerRetransmit.symbol} for a timer the mirror never armed ({u})")
    pure () : Leanux.M Unit).run w) = _
  rw [StateT.run_bind, peek]
  have getWGProduct : (getWG : Leanux.M WGWorld) = (fun state => .ok (state.wg, state)) := rfl
  have sameTimer : (PeerTimer.retransmitHandshake != PeerTimer.retransmitHandshake) = false := rfl
  simp [getWGProduct, registered, sameTimer, StateT.run, Bind.bind, Pure.pure,
    StateT.bind, StateT.pure, Except.bind, Except.pure]

theorem fire_total (w after : World) (d : Device) (p : Peer) (pid : PeerId)
    (horizon : UInt64) (we : WheelEntry) (start stop : List UInt8) (rest suffix : List HiddenRecord)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p)
    (present : w.ambient.hidden = some (sectionRecord true start :: rest))
    (startSize : start.length = 16) (stopSize : stop.length = 8)
    (nonzero : recordWordOf start 1 ≠ 0)
    (registered : w.wg.timerUnits.find? (·.1 == recordWordOf start 1) =
      some (recordWordOf start 1,pid,.retransmitHandshake))
    (due : pid ∈ duePeers d .retransmitHandshake horizon)
    (callback : (liftWG (expiredRetransmitHandshake pid)).run
      (sectionEntry (dispatchEntry w d p pid we) rest) = .ok ((),after))
    (ended : after.ambient.hidden = some (sectionRecord false stop :: suffix)) :
    (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we none).run w =
      .ok ((),{after with
        wg := {after.wg with timerPassStep := none}
        ambient := {after.ambient with hidden := some suffix}}) := by
  have selected := selection w d horizon pid we start rest device present startSize nonzero registered due
  rw [fireTimer_source, StateT.run_bind, selected]
  change (fireWheelSelected .timerRetransmit pid .retransmitHandshake we).run w = _
  change ((do
    liftWG (delTimer pid .retransmitHandshake)
    modifyWG fun state => {state with timerPassStep := some we.bucketExpiry}
    runTimerSection .timerRetransmit (liftWG (expiredRetransmitHandshake pid))
    modifyWG fun state => {state with timerPassStep := none}).run w) = _
  rw [StateT.run_bind]
  rw [detach w d p pid device resident]
  change ((do
    runTimerSection .timerRetransmit (liftWG (expiredRetransmitHandshake pid))
    modifyWG fun s => {s with timerPassStep := none}).run (dispatchEntry w d p pid we)) = _
  have sectionRun := section_total (liftWG (expiredRetransmitHandshake pid))
    (dispatchEntry w d p pid we) after start stop rest suffix present startSize stopSize callback ended
  rw [StateT.run_bind, sectionRun]
  rfl
theorem fire_ready_run (w : World) (d : Device) (p : Peer) (pid : PeerId) (horizon : UInt64) (we : WheelEntry)
    (start cache clock queue stop : List UInt8) (suffix : List HiddenRecord)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p)
    (due : pid ∈ duePeers d .retransmitHandshake horizon)
    (startLen : start.length=16) (stopLen : stop.length=8)
    (cacheLen : cache.length=8) (clockLen : clock.length=8) (queueLen : queue.length=16)
    (nonzero : recordWordOf start 1 ≠ 0)
    (registered : w.wg.timerUnits.find? (·.1 == recordWordOf start 1) =
      some (recordWordOf start 1,pid,.retransmitHandshake))
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES)
    (alive : p.isDead=false) (pending : p.handshakePending=false)
    (positive : 0<p.refcount) (bounded : p.refcount+1<2^31)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64*NSEC_PER_SEC64 ≤ (RetryReady.word clock).toInt64)
    (mode : w.ambient.armRecords=true) (cacheMode : w.wg.dstCacheRecords=true)
    (unit : w.ambient.unitPeers.find? (fun e => e.2.1 == Worker.sendWorker.index && e.2.2 == pid) =
      some (recordWordOf queue 0,Worker.sendWorker.index,pid))
    (records : w.ambient.hidden = some (suppliedRecords start cache clock queue stop suffix)) :
    (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we none).run w = .ok ((),fireResult w d p pid cache clock suffix) := by
  let rest := {site:=150,bytes:=cache}::{site:=6,bytes:=clock}::
    {site:=(HiddenSite.queued .sendWorker).info.id,bytes:=queue}::sectionRecord false stop::suffix
  have afterResident : (detachedDevice d p pid).peers[pid]? =
      some (detachedPeer p) := by
    simp [detachedDevice]
  have callback := RetryReady.callback_run pid (detachedDevice d p pid)
    (detachedPeer p) cache clock queue (sectionRecord false stop::suffix)
    (sectionEntry (dispatchEntry w d p pid we) rest)
    afterResident rfl limit alive pending positive bounded expired cacheLen clockLen queueLen
    mode cacheMode unit rfl
  have fired := fire_total w _ d p pid horizon we start stop rest suffix device resident
    records startLen stopLen nonzero registered due callback rfl
  simpa [fireResult, sectionEntry, dispatchEntry, afterDetach] using fired


end Leanux.Proofs.WG.TimerDiscipline.FireReady
