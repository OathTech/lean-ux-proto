import Leanux.Proofs.WG.TimerDiscipline.FireReadySource

/-! Corrected Product outcome for the actual selected retransmit wheel unit, with arbitrary wheel entry and no assertion of horizon dispatch completeness. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.FireReady
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline
theorem fire_outcome (d : Device) (p : Peer) (pid : PeerId) (horizon : UInt64) (we : WheelEntry)
    (start cache clock queue stop : List UInt8) (suffix : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (due : pid ∈ duePeers d .retransmitHandshake horizon)
    (startLen : start.length=16) (stopLen : stop.length=8)
    (cacheLen : cache.length=8) (clockLen : clock.length=8) (queueLen : queue.length=16)
    (nonzero : recordWordOf start 1 ≠ 0)
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES)
    (alive : p.isDead=false) (pending : p.handshakePending=false)
    (positive : 0<p.refcount) (bounded : p.refcount+1<2^31)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64*NSEC_PER_SEC64 ≤ (RetryReady.word clock).toInt64) :
    Campaign2.Product.Observes (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we none)
      (fun s => s.wg.device=some d ∧
        s.ambient.hidden=some (suppliedRecords start cache clock queue stop suffix) ∧
        s.ambient.armRecords=true ∧ s.wg.dstCacheRecords=true ∧
        s.wg.timerUnits.find? (·.1 == recordWordOf start 1) =
          some (recordWordOf start 1,pid,.retransmitHandshake) ∧
        s.ambient.unitPeers.find? (fun e => e.2.1 == Worker.sendWorker.index && e.2.2 == pid) =
          some (recordWordOf queue 0,Worker.sendWorker.index,pid))
      (fun entry outcome => outcome=.ok ((),fireView entry d p pid cache clock suffix)) := by
  intro w pre
  have run := fire_ready_run w d p pid horizon we start cache clock queue stop suffix
    pre.1 resident due startLen stopLen cacheLen clockLen queueLen nonzero pre.2.2.2.2.1
    limit alive pending positive bounded expired pre.2.2.1 pre.2.2.2.1 pre.2.2.2.2.2 pre.2.1
  unfold Campaign2.Product.observeResult
  rw [run]
  rfl


end Leanux.Proofs.WG.TimerDiscipline.FireReady
