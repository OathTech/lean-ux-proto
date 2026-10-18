import Leanux.Proofs.WG.TransmitSecurity.NonceDeferredFrames

/-! Source-exact deferred scheduling and timer passes. Every committed native
timer callback shares the nonce journal with the crypt workers it causes. -/
set_option pp.structureInstances false
set_option maxHeartbeats 600000
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def cryptObserved : PrefixM Allocation Unit := do
  scheduleObserved none
  liftPrefix Env.deliverSent

def sendWorkersObserved : PrefixM Allocation Unit := do
  if (← liftPrefix getWG).dev.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    liftPrefix Env.runOneSendWorker
    scheduleObserved none
  liftPrefix (budgetExhausted "the send work queue")

def afterXmitObserved : PrefixM Allocation Unit := do
  let some d := (← liftPrefix getWG).dev | return
  let crypt := !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
  if crypt && !d.sendWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_xmit queued crypt work and a handshake (their order)")
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if crypt then
    cryptObserved
    let d ← liftPrefix (liftWG getDev)
    liftPrefix (Env.requireDrained "wg_xmit queued" [!d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  sendWorkersObserved

def timerSectionObserved (worker : Worker) (body : PrefixM Allocation Unit) : PrefixM Allocation Unit := do
  if worker.timer?.isNone then liftPrefix (invariant s!"{worker.symbol} is not a timer callback")
  liftPrefix (modifyAmbient fun s => {s with fired := s.fired.push worker.symbol})
  runWorkerPrefix worker body

def timersObserved (jPass : UInt64) : PrefixM Allocation Bool := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix Env.peekNextSite | break
    let d ← liftPrefix (liftWG getDev)
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          liftPrefix (Env.requireStepComplete b)
          step := none
        if d.clearWorkQueue.isEmpty then break
        liftPrefix Env.runOneClearWorker
      else
        let some (pid, t, we) := TimerWheel.nextDue d jPass
          | liftPrefix (throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}"))
        let expected ← liftPrefix (Env.timerWorker t)
        if w != expected then
          liftPrefix (throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}"))
        if let some u ← liftPrefix (peekUnit w) then
          match (← liftPrefix getWG).timerUnits.find? (·.1 == u) with
          | some (_, pid', t') =>
            if pid' != pid || t' != t then
              liftPrefix (throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}"))
          | none => liftPrefix (throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})"))
        if let some b := step then
          if b != we.bucketExpiry then liftPrefix (Env.requireStepComplete b)
        liftPrefix (liftWG (delTimer pid t))
        liftPrefix (modifyWG fun s => {s with timerPassStep := some we.bucketExpiry})
        timerSectionObserved w (liftWGObserver (timerObserved pid t))
        liftPrefix (modifyWG fun s => {s with timerPassStep := none})
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        liftPrefix (Env.requireStepComplete b)
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then liftPrefix Env.runOneSendWorker
      else
        cryptObserved
        if (← liftPrefix Env.peekNextSite) == some site then break
  if let some b := step then liftPrefix (Env.requireStepComplete b)
  if fired then
    liftPrefix Env.deliverSent
    let d ← liftPrefix (liftWG getDev)
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

def placeholderTimersObserved (jHi : UInt64) : PrefixM Allocation Unit := do
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  if (← liftPrefix getWG).dev.isNone then return
  let pending := (← liftPrefix (liftWG getDev)).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let some (pid, t, _) := TimerWheel.nextDue (← liftPrefix (liftWG getDev)) jHi | break
    liftPrefix (liftWG (delTimer pid t))
    timerSectionObserved (← liftPrefix (Env.timerWorker t)) (liftWGObserver (timerObserved pid t))
  cryptObserved
  sendWorkersObserved
  for _ in [0:(← liftPrefix (liftWG getDev)).clearWorkQueue.length + 1] do
    if (← liftPrefix (liftWG getDev)).clearWorkQueue.isEmpty then break
    liftPrefix Env.runOneClearWorker

def idleTimersObserved : PrefixM Allocation Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.traceBound.toUInt64 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then placeholderTimersObserved jHi else discard <| timersObserved jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation"))
  discard <| timersObserved jEnd
  liftPrefix (Env.requireNothingDue jEnd)
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => {w with jiffiesLast := some j})

def afterAdvanceObserved : PrefixM Allocation Unit := do
  let w ← liftPrefix getWG
  let a ← liftPrefix getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then placeholderTimersObserved jHi else discard <| timersObserved jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance"))
  let some (j0, j1) := (← liftPrefix getEnv).lastAdvance | liftPrefix (invariant "afterAdvance without an advance")
  let jPass := if timeAfter jEnd j1 then jEnd else j0
  discard <| timersObserved jPass
  liftPrefix (Env.requireNothingDue jPass)
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modifyWG fun w => {w with jiffiesLast := some j})

macro "nonce_deferred_erasure" : tactic => `(tactic| first
  | maintenance_intro
  | contradiction
  | timer_audit_stopped
  | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
  | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
  | (maintenance_head ForIn.forIn; apply erasesPrefix_range)
  | (maintenance_head Bind.bind; apply erasesPrefix_bind)
  | (maintenance_head ite; apply erasesPrefix_ite)
  | timer_audit_erases_join
  | timer_audit_erases_join_use
  | timer_audit_reduce
  | timer_audit_reduce_match
  | timer_audit_cases
  | (with_reducible split))

theorem cryptObserved_erases : ErasesPrefix cryptObserved Env.runCryptWorkers :=
  erasesPrefix_bind (scheduleObserved_erases none) (fun _ => erasesPrefix_lift _)

theorem sendWorkersObserved_erases : ErasesPrefix sendWorkersObserved Env.runSendWorkers := by
  unfold sendWorkersObserved Env.runSendWorkers
  repeat' first | with_reducible exact scheduleObserved_erases _ | nonce_deferred_erasure

theorem afterXmitObserved_erases : ErasesPrefix afterXmitObserved Env.afterXmit := by
  unfold afterXmitObserved Env.afterXmit
  repeat' first
    | with_reducible exact cryptObserved_erases
    | with_reducible exact sendWorkersObserved_erases
    | nonce_deferred_erasure

theorem timerSectionObserved_erases (worker : Worker) {body : PrefixM Allocation Unit} {native : Leanux.M Unit}
    (erases : ErasesPrefix body native) :
    ErasesPrefix (timerSectionObserved worker body) (Env.runTimerSection worker native) := by
  unfold timerSectionObserved Env.runTimerSection
  repeat' first
    | with_reducible exact runWorkerPrefix_erases worker erases
    | nonce_deferred_erasure

theorem timersObserved_erases (jPass : UInt64) : ErasesPrefix (timersObserved jPass) (Env.runTimers jPass) := by
  unfold timersObserved Env.runTimers
  repeat' first
    | with_reducible exact cryptObserved_erases
    | (maintenance_head timerSectionObserved; exact timerSectionObserved_erases _ (liftWGObserver_erases (timerObserved_erases _ _)))
    | nonce_deferred_erasure

theorem placeholderTimersObserved_erases (jHi : UInt64) :
    ErasesPrefix (placeholderTimersObserved jHi) (Env.runTimersPlaceholder jHi) := by
  unfold placeholderTimersObserved Env.runTimersPlaceholder
  repeat' first
    | with_reducible exact cryptObserved_erases
    | with_reducible exact sendWorkersObserved_erases
    | (maintenance_head timerSectionObserved; exact timerSectionObserved_erases _ (liftWGObserver_erases (timerObserved_erases _ _)))
    | nonce_deferred_erasure

theorem idleTimersObserved_erases : ErasesPrefix idleTimersObserved Env.idleTimers := by
  unfold idleTimersObserved Env.idleTimers
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact timersObserved_erases _
    | with_reducible exact placeholderTimersObserved_erases _
    | nonce_deferred_erasure

theorem afterAdvanceObserved_erases : ErasesPrefix afterAdvanceObserved Env.afterAdvance := by
  unfold afterAdvanceObserved Env.afterAdvance
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact timersObserved_erases _
    | with_reducible exact placeholderTimersObserved_erases _
    | nonce_deferred_erasure

end Leanux.Proofs.WG.TransmitSecurity.Nonce
