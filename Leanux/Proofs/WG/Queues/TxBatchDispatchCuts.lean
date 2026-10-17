import Leanux.Proofs.WG.Queues.TxDispatchCuts

namespace Leanux.Proofs.WG.Queues.TxDisposition.BatchDispatchCuts
open Leanux Leanux.WG Leanux.Env

/-- The original final publication before deferred batch work starts. -/
def finishBegin (cqes : List Int) : Leanux.M Unit := do
  modifyAmbient fun w=>{w with extraOut:=[("cqes",Lean.toJson cqes)]}
  modifyWG fun w=>{w with queuedThisCall:=[]}

def afterReset : Leanux.M Unit := do
  if (← getAmbient).hidden.isNone then
    runCryptWorkers
    runSendWorkers
    return
  for _ in [0:(← recordBudget)] do
    schedule
    if (← peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← getDev).sendWorkQueue.isEmpty then
      runOneSendWorker
    else break
  let d ← getDev
  requireDrained "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0]
  deliverSent

theorem finish_factor (entries : List BatchItem) (cqes : List Int) :
    ProducerCuts.finish entries cqes = (do finishBegin cqes; afterReset; return entries.length) := by
  unfold ProducerCuts.finish Env.afterBatch finishBegin afterReset
  simp only [bind_assoc]

def recordedBody (stack : Option Worker) (next : Option Nat) :
    Leanux.M (ForInStep (Option Unit × Unit)) := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  if let some (w,true) := next.bind sectionOf then
    if ← Env.dispatch w then return .yield (none,()) else return .done (some (),())
  if next == some netRx && (← getDev).peers.toList.any (·.2.napiScheduled) then
    napiSoftirq
    if (← peekHiddenSite) == some netRx then return .done (some (),())
    return .yield (none,())
  match ← (← getAmbient).suspended.filterM Activation.consistent with
  | []=>return .done (some (),())
  | [a]=>
    if let some w := stack then
      if ← Activation.hasWork {worker:=w} then
        unsupported "the records do not determine which suspended worker resumed"
    modifyAmbient fun s=>{s with suspended:=s.suspended.filter (· != a)}
    Activation.run a
    return .yield (none,())
  | _=>unsupported "the records do not determine which suspended worker resumed"

def scheduleBody (stack : Option Worker) (_state : Option Unit × Unit) :
    Leanux.M (ForInStep (Option Unit × Unit)) := do
  if (← getAmbient).hidden.isNone then
    let d ← getDev
    let next := [Worker.receiveWorker,.decryptWorker,.encryptWorker,.txWorker].find? fun w=>
      match w with
      | .receiveWorker=> !d.handshakeQueue.empty
      | .decryptWorker=> !d.decryptQueue.empty
      | .encryptWorker=> !d.encryptQueue.empty
      | _=> !d.txWorkQueue.isEmpty
    let some w:=next | return .done (some (),())
    if !(← Env.dispatch w) then invariant s!"{w.symbol} has work but was not dispatched"
    return .yield (none,())
  let next ← peekHiddenSite
  recordedBody stack next

def scheduleRun (stack : Option Worker) : Leanux.M Unit := do
  let bound ← recordBudget
  let result ← forIn [0:bound] (none,()) (fun _ state=>scheduleBody stack state)
  match result.1 with
  | some value=>return value
  | none=>budgetExhausted "the scheduler loop"

theorem schedule_factor (stack : Option Worker) : Env.schedule stack=scheduleRun stack := by
  unfold Env.schedule scheduleRun scheduleBody recordedBody
  dsimp only
  apply RxCredits.bind_congr_source (m:=Leanux.M)
  intro bound
  congr 1
  funext option world
  rcases option with ⟨option,ignored⟩
  cases ignored
  cases option with
  | none=>rfl
  | some value=>cases value; rfl

theorem recorded_encrypt (stack : Option Worker) :
    recordedBody stack (some (HiddenSite.sectionStart .encryptWorker).info.id) = (do
      if ← Env.dispatch .encryptWorker then return .yield (none,()) else return .done (some (),())) := rfl

theorem recorded_tx (stack : Option Worker) :
    recordedBody stack (some (HiddenSite.sectionStart .txWorker).info.id) = (do
      if ← Env.dispatch .txWorker then return .yield (none,()) else return .done (some (),())) := rfl

end Leanux.Proofs.WG.Queues.TxDisposition.BatchDispatchCuts
