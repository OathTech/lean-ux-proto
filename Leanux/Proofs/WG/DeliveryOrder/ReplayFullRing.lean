import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.WG.Environment.BatchSource
import Leanux.Proofs.WG.Queues.TxDisposition
import Leanux.Proofs.WG.Queues.TxProducerCuts
import Leanux.Proofs.WG.Queues.TxBatchDispatchCuts
import Leanux.Proofs.WG.Queues.TxDispatchCuts
import Leanux.Proofs.WG.Queues.RunnerOperation
import Leanux.Proofs.WG.Queues.SyscallEntryCuts

/-! Compiled executable checks of generated explicit records, not a Linux capture.
The initialized checkpoints and native source cuts are existing definitions. -/
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Leanux.Proofs.WG

private def require (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def checked {α : Type} (label : String) (a : Except Stop α) : IO α :=
  match a with
  | .error e => throw (IO.userError s!"{label}: {e.message}")
  | .ok value => pure value

private def device (label : String) (w : World) : IO Device :=
  match w.wg.dev with
  | none => throw (IO.userError s!"{label}: missing device")
  | some d => pure d

private def peer (label : String) (d : Device) : IO Peer :=
  match d.peers[0]? with
  | none => throw (IO.userError s!"{label}: missing peer 0")
  | some p => pure p

private def choices (w : World) (decision : Decision) : List Bool :=
  w.ambient.steps.toList.filterMap fun s => if s.decision == decision then some s.outcome else none

private def occupied (ring : PtrRing (List SkbId)) : List Nat :=
  (List.range ring.size).filter fun n => ((ring.slots[n]?).getD none).isSome

private def sameQueueResult (a b : World) : Bool :=
  a.wg.dev == b.wg.dev && a.wg.sent == b.wg.sent &&
  a.ambient.hidden == b.ambient.hidden && a.ambient.steps == b.ambient.steps &&
  a.ambient.suspended == b.ambient.suspended && a.ambient.pendingWork == b.ambient.pendingWork

def main : IO UInt32 := do
  let trace ← match Json.parse (← (← IO.getStdin).getLine) >>= parseTrace with
    | .error e => throw (IO.userError e)
    | .ok t => pure t
  require (trace.id == "w7_ring_wrap" && trace.ops.size == 8 && trace.hidden.isSome && !trace.armRecords)
    "expected original eight-operation W7 recipe with explicit records"
  let original ← match executeTrace trace false with
    | .error (i,e) => throw (IO.userError s!"original operation {i}: {e.message}")
    | .ok j => pure j
  let (observed, checkpoints) ← match (executeTraceCheckpoints (fun _ w => w) trace false).run [] with
    | .error (i,e) => throw (IO.userError s!"checkpoint operation {i}: {e.message}")
    | .ok r => pure r
  require (observed.compress == original.compress && checkpoints.length == 8)
    "original/checkpoint result differs"
  let some session := checkpoints[3]? | throw (IO.userError "missing session cut")
  let some before := checkpoints[4]? | throw (IO.userError "missing burst entry")
  let some after := checkpoints[5]? | throw (IO.userError "missing burst return")
  let d0 ← device "session" session
  let d ← device "burst entry" before
  let da ← device "burst return" after
  require (d0.encryptQueue.producer == 1 && d0.encryptQueue.consumerHead == 1 &&
    d0.encryptQueue.consumerTail == 0 && occupied d0.encryptQueue == [0]) "wrong first carried slot"
  require (d.encryptQueue.producer == 2 && d.encryptQueue.consumerHead == 2 &&
    d.encryptQueue.consumerTail == 0 && occupied d.encryptQueue == [0,1] &&
    d.encryptQueue.items.isEmpty && d.txSkbs.isEmpty && (← peer "burst entry" d).txQueue.all.isEmpty)
    "entry is not exactly two stale carried slots with no pending TX items"
  let some (Operation.wgBatch items 1000) := trace.ops[5]? | throw (IO.userError "wrong burst operation")
  require (items.length == 1024) "burst is not 1024 original items"
  require (items.all fun item => match item with
    | .xmit 4 0x0a000001 payload _ => payload.length == 1
    | _ => false) "burst differs from original singleton IPv4 sends"
  require (choices after .createDataEpipe == List.replicate 1022 false ++ [true,true] &&
    choices after .enqueueRingFull == List.replicate 1022 false ++ [true,true] &&
    choices after .enqueuePeerQueueFull == List.replicate 1024 false &&
    choices after .txCrypted == List.replicate 1022 true ++ [false,false])
    "original syscall did not take exact refusal and DEAD disposal positions"
  -- Named original runner preparation and actual syscall-entry prefix.
  let observations ← match original.getObjValAs? (Array Json) "observations" with
    | .error e=>throw (IO.userError e)
    | .ok xs=>pure xs
  let mut results : Array Int := #[]
  for observation in observations.toList.take 5 do
    let result ← match observation.getObjValAs? Int "ret" with
      | .error e=>throw (IO.userError e)
      | .ok ret=>pure ret
    results:=results.push result
  require (results.size==5) "missing original result prefix"
  let prepared := Queues.RxCredits.RunnerOperation.prepare trace
    (before,results,#[],#[],#[],#[])
  let (entryResult,entryHistory) := runPrefix
    (Queues.RxCredits.SyscallEntryCuts.enter (.wgBatch items 1000)) prepared []
  let (_,start) ← checked "actual syscall entry" entryResult
  require entryHistory.isEmpty "entry unexpectedly emitted history"
  let (batchRet, batchEnd) ← checked "original native batch" ((Env.batch items).run start)
  require (batchRet == 1024 && batchEnd.wg.dev == after.wg.dev)
    "original native batch does not match actual syscall device endpoint"
  let (batchDevice,producerStart) ← checked "actual batch front"
    (Queues.TxDisposition.ProducerCuts.front.run start)
  let mut current := producerStart
  let mut cqes : List Int := []
  let mut produced : List (List SkbId) := []
  let mut refused : List (List SkbId) := []
  for (item,index) in items.zipIdx do
    let old ← device "producer before" current
    let oldPeer ← peer "producer before" old
    let (result,next) ← checked s!"producer item {index}" ((Environment.batchItemSource batchDevice cqes item).run current)
    let .yield nextCqes := result | throw (IO.userError "original all-xmit item terminated loop")
    let now ← device "producer after" next
    let nowPeer ← peer "producer after" now
    let fresh := [old.nextSkb]
    require (now.nextSkb == old.nextSkb + 1 && nowPeer.txQueue.all == oldPeer.txQueue.all ++ [fresh] &&
      nextCqes == cqes ++ [1]) s!"item {index} did not allocate/queue its exact singleton"
    let some packet := now.txSkbs[old.nextSkb]? | throw (IO.userError "missing fresh TX allocation")
    if index < 1022 then
      require (packet.state == .uncrypted && now.encryptQueue.items == old.encryptQueue.items ++ [fresh])
        s!"accepted item {index} lacks exact logical enqueue"
    else
      require (packet.state == .dead && now.encryptQueue == old.encryptQueue &&
        choices next .createDataEpipe == List.replicate 1022 false ++ List.replicate (index-1021) true)
        s!"refused item {index} lacks exact DEAD publication without enqueue"
      refused := refused ++ [fresh]
    produced := produced ++ [fresh]
    cqes := nextCqes
    current := next
  require (refused == produced.drop 1022 && refused.length == 2) "wrong refused identities"
  let producedWorld := current
  let dp ← device "producer complete" producedWorld
  require (dp.encryptQueue.items == produced.take 1022 && dp.encryptQueue.producer == 0 &&
    dp.encryptQueue.consumerHead == 2 && dp.encryptQueue.consumerTail == 0 &&
    (← peer "producer complete" dp).txQueue.all == produced) "wrong complete producer cut"
  -- Exact finish publication, recorded afterBatch entry, then scheduler entry.
  let (_,deferredStart) ← checked "actual batch finish prefix"
    ((Queues.TxDisposition.BatchDispatchCuts.finishBegin cqes).run producedWorld)
  let (deferredAmbient,deferredRead) ← checked "actual afterBatch mode"
    ((show Leanux.M Ambient from getAmbient).run deferredStart)
  require deferredAmbient.hidden.isSome "expected recorded afterBatch branch"
  let (outerBound,schedulerStart) ← checked "actual afterBatch bound"
    ((show Leanux.M Nat from recordBudget).run deferredRead)
  require (outerBound>0) "afterBatch has no iteration"
  let (scheduleBound,scheduleStart) ← checked "actual scheduler bound"
    ((show Leanux.M Nat from recordBudget).run schedulerStart)
  require (scheduleBound>=3) "scheduler lacks the two dispatches and final turn"
  let (encryptAmbient,encryptRead) ← checked "actual scheduler mode"
    ((show Leanux.M Ambient from getAmbient).run scheduleStart)
  require encryptAmbient.hidden.isSome "expected recorded scheduler branch"
  let (encryptSite,encryptEntry) ← checked "actual scheduler encrypt selection"
    ((show Leanux.M (Option Nat) from peekHiddenSite).run encryptRead)
  require (encryptSite==some (HiddenSite.sectionStart .encryptWorker).info.id)
    "original scheduler did not select encryption"
  let (encStarted, encrypted) ← checked "actual encrypt dispatch" ((Env.dispatch .encryptWorker).run encryptEntry)
  require encStarted "encrypt activation did not dispatch"
  let de ← device "encrypt complete" encrypted
  for item in refused do
    let some id := item.head? | throw (IO.userError "empty refused item")
    require ((de.txSkbs[id]?).any (·.state == .dead)) "encryption changed a refused head"
  let (txAmbient,txRead) ← checked "actual next scheduler mode"
    ((show Leanux.M Ambient from getAmbient).run encrypted)
  require txAmbient.hidden.isSome "expected next recorded scheduler branch"
  let (txSite,txEntry) ← checked "actual scheduler TX selection"
    ((show Leanux.M (Option Nat) from peekHiddenSite).run txRead)
  require (txSite==some (HiddenSite.sectionStart .txWorker).info.id)
    "original scheduler did not select TX"
  let (txStarted, txEnd) ← checked "actual TX dispatch" ((Env.dispatch .txWorker).run txEntry)
  require txStarted "TX activation did not dispatch"
  -- The actual native dispatch prefix retains unit resolution and all guards.
  let (selection,txStart) ← checked "actual TX dispatch prefix"
    ((Queues.TxDisposition.DispatchCuts.begin .txWorker).run txEntry)
  let some activation := selection | throw (IO.userError "TX prefix returned no activation")
  require (activation.worker==.txWorker && activation.pid==some 0) "unexpected selected TX unit"
  let (occupancy,txStart) ← checked "actual TX occupancy" ((Env.Activation.occupancy activation).run txStart)
  require (occupancy==produced.length) "actual activation bound differs from produced items"
  let mut txCurrent := txStart
  let mut act := activation
  let mut disposed : List (List SkbId) := []
  for (item,index) in produced.zipIdx do
    let old ← device "TX before" txCurrent
    require ((← peer "TX before" old).txQueue.all.head? == some item) "TX source order changed"
    let (result,next) ← checked s!"actual TX loop body {index}"
      ((Queues.TxDisposition.DispatchCuts.body (none,act)).run txCurrent)
    let .yield (_,nextAct) := result | throw (IO.userError "TX body did not continue under recorded schedule")
    require (nextAct.iterations==act.iterations+1) "TX activation iteration counter changed incorrectly"
    let now ← device "TX after" next
    require (item.all fun id => (now.txSkbs[id]?).isNone) "TX failed to release its selected item"
    if index >= 1022 then
      let (_,stepEntry) ← checked "actual cryptAhead prefix" ((Env.cryptAhead 0).run txCurrent)
      let (receipt,events) := runPrefix (Queues.TxDisposition.step 0) stepEntry []
      let (_,receiptWorld) ← checked "existing disposition observer" receipt
      require (receiptWorld.wg.dev == next.wg.dev &&
        (events.filterMap (fun e => match e with | .removed pid actual => some (pid,actual) | _ => none)) == [(0,item)] &&
        (events.filterMap (fun e => match e with
          | .access (.packet (.release (.inl id) stamp)) => some (id,stamp)
          | _ => none)) == item.map (fun id => (id,(old.ifindex,id+1))) &&
        !(events.any (fun e => match e with | .completion .. => true | _ => false)))
        "refused identity did not take actual removal without completion"
      disposed := disposed ++ [item]
    txCurrent := next
    act := nextAct
  let (termination,txDone) ← checked "actual final TX loop body"
    ((Queues.TxDisposition.DispatchCuts.body (none,act)).run txCurrent)
  let .done (some (),_) := termination | throw (IO.userError "TX loop did not return at its final poll")
  require (sameQueueResult txDone txEnd && disposed == refused)
    "sequential selected cuts differ from actual whole TX dispatch"
  let (schedulerExit,_) ← checked "actual scheduler final turn"
    ((Queues.TxDisposition.BatchDispatchCuts.scheduleBody none (none,())).run txDone)
  let .done (some (),_) := schedulerExit | throw (IO.userError "scheduler did not end after the two recorded dispatches")
  let (_,finished) ← checked "actual batch finish" ((Queues.TxDisposition.ProducerCuts.finish items cqes).run producedWorld)
  require (sameQueueResult finished batchEnd && da.txSkbs.isEmpty &&
    da.encryptQueue.items.isEmpty && (← peer "final" da).txQueue.all.isEmpty &&
    occupied da.encryptQueue == [] && da.txErrors == d.txErrors && da.txDropped == d.txDropped)
    "actual full drain/endpoint differs or refused packets changed device drop counters"
  (← IO.getStdout).putStrLn (Json.mkObj [
    ("id",toJson trace.id),("accepted",toJson true),
    ("record_origin",toJson "generated explicit inputs, not a Linux capture"),
    ("carried_slots",toJson ([0,1] : List Nat)),("producer_items",toJson produced.length),
    ("epipe_positions_zero_based",toJson ([1022,1023] : List Nat)),
    ("refused_items",toJson refused),("disposed_items",toJson disposed),
    ("disposed_packet_stamps",toJson (disposed.flatten.map fun id => (d.ifindex,id+1))),
    ("logical_enqueued",toJson (produced.take 1022).length),
    ("original_json_matches",toJson true),
    ("claim",toJson "compiled concrete acceptance and checked existing source cuts; no universal initialized disposal theorem")]).compress
  return 0
