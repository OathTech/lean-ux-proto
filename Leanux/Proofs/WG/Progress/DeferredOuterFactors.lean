import Leanux.Proofs.WG.Progress.TimerWaitSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DeferredOuter
open Leanux Leanux.WG Leanux.Env

/-- Original after-transmit branch with its two actual worker callbacks. -/
def afterXmitWith (cryptWork sendWork : Leanux.M Unit) : Leanux.M Unit := do
  let some d := (← getWG).dev | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    unsupported "wg_xmit queued crypt work and a handshake (their order)"
  modifyWG fun w => { w with queuedThisCall := [] }
  if crypt then
    cryptWork
    let d ← getDev
    requireDrained "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty]
  sendWork

theorem afterXmit_source :
    Env.afterXmit = afterXmitWith runCryptWorkers runSendWorkers := rfl

/-- Original wait modes, with the existing checked end-read suffix. -/
def idleWith (timers : UInt64 → Leanux.M Bool)
    (placeholder : UInt64 → Leanux.M Unit) : Leanux.M Unit := do
  let w ← getWG
  let a ← getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then placeholder jHi else discard <| timers jHi
    return
  let some jEnd ← peekSiteU64 .jiffiesEnd
    | throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation")
  discard <| timers jEnd
  timerWaitFinish jEnd jEnd

theorem idle_source :
    Env.idleTimers = idleWith runTimers runTimersPlaceholder := rfl

end Leanux.Proofs.WG.Progress.DeferredOuter
