import Leanux.Proofs.WG.TimerDiscipline.RetryReadyModel
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Total original retry branch: increment, endpoint/cache reset, reference
acquisition and queued send work, with exact supplied-record and state effects. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline.RetryReady
open Leanux Leanux.WG Campaign2

theorem callback_run (pid : PeerId) (d : Device) (p : Peer)
    (cache clock queue : List UInt8) (rest : List HiddenRecord) (w : World)
    (resident : d.peers[pid]? = some p) (device : w.k.wg = some d)
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES)
    (alive : p.isDead = false) (pending : p.handshakePending = false)
    (positive : 0 < p.refcount) (bounded : p.refcount+1 < 2^31)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ (word clock).toInt64)
    (cacheLen : cache.length=8) (clockLen : clock.length=8) (queueLen : queue.length=16)
    (mode : w.armRecords=true) (cacheMode : w.dstCacheRecords=true)
    (unit : w.unitPeers.find? (fun e => e.2.1 == Worker.sendWorker.index && e.2.2 == pid) =
      some (recordWordOf queue 0,Worker.sendWorker.index,pid))
    (records : w.hidden = some ({site:=150,bytes:=cache}::{site:=6,bytes:=clock}::
      {site:=(HiddenSite.queued .sendWorker).info.id,bytes:=queue}::rest)) :
    (expiredRetransmitHandshake pid).run w = .ok ((),{w with
      k:={w.k with wg:=some (result d pid p cache)}
      hidden:=some rest
      steps:=decisions p clock w.netRxSection w.steps
      queuedThisCall:=pid::w.queuedThisCall}) := by
  have cachePassive : HiddenSite.passive 150 = false := by decide
  have clockPassive : HiddenSite.passive 6 = false := by decide
  have queuePassive : HiddenSite.passive (HiddenSite.queued .sendWorker).info.id = false := by decide
  have cacheDrop : cache.drop 8=[] := by simp [←cacheLen]
  have cacheTake : cache.take 8=cache := by simp [←cacheLen]
  have clockDrop : clock.drop 8=[] := by simp [←clockLen]
  have clockTake : clock.take 8=clock := by simp [←clockLen]
  have queueDrop : queue.drop 16=[] := by simp [←queueLen]
  have queueTake : queue.take 16=queue := by simp [←queueLen]
  have notLimit : ¬ MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts := by omega
  have zeroTest : (p.refcount == 0) = false := by simp; omega
  have clockExpired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤
      Int64.ofNat (clock.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0) := expired
  have below : ¬ p.refcount+1 ≥ 2^31 := by omega
  have noOverflow : ¬ 2147483647 ≤ p.refcount := by simpa using below
  simp only [HiddenSite.info,Worker.queueId,Worker.index] at unit queuePassive records
  simp [expiredRetransmitHandshake, clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset,
    sendQueuedHandshakeInitiation, requireNotPending, branchExpired, birthdateTest,
    peerGet, refcountInc, recordQueued, branch, branchCmp,
    getPeer,getDev,getK,setPeer,modifyDev,modifyK,
    device,resident,notLimit,alive,pending,zeroTest,noOverflow,clockExpired,
    hiddenJiffies,hiddenClock64,hidden,skipAmbient,noteNetRxStart,
    mode,cacheMode,records,unit,cacheLen,clockLen,queueLen,cacheDrop,cacheTake,clockDrop,clockTake,
    queueDrop,queueTake,cachePassive,clockPassive,queuePassive,
    HiddenSite.info,Worker.queueId,Worker.sectionId,Worker.index,
    result,queued,acquired,dropped,reset,cleared,bumped,decisions,word,
    StateT.run,Bind.bind,Pure.pure,get,getThe,MonadStateOf.get,set,modify,modifyGet,
    StateT.bind,StateT.pure,StateT.get,StateT.set,MonadStateOf.modifyGet,StateT.modifyGet,
    Except.bind,Except.pure]

end Leanux.Proofs.WG.TimerDiscipline.RetryReady
