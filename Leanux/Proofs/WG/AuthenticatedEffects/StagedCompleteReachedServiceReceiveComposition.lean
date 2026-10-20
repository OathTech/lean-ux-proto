import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServiceRunnerCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveEncryptionComposition

/-! Join the expanded receive scheduler, work services and concrete timers
to the initialized runner. Four packet families, the flushed protocol sender
and twelve dispatch bodies remain explicit; universal T2 coverage stays open. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.ReceiveComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def schedulerPoints (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (worker : Iteration.Points.ChildPoints) : Scheduler.Points.ChildPoints :=
  ReceiveWorker.Composition.schedulerPoints (StagingExpanded.consumePoints consume) napi
    (Prepare.Points.iterationPoints (EncryptionCallback.iterationPoints worker))

def servicePoints (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (worker : Iteration.Points.ChildPoints) (work : WorkService.Points.ChildPoints) : Points.ChildPoints :=
  Expanded.points (schedulerPoints consume napi worker) (Expanded.workPoints work)

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

noncomputable def schedulerChildren
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (receive : ReceiveWorker.Composition.StagedReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good)
    (workers : ReceiveWorker.Composition.EncryptionWorkerOther nativeConsume insideConsume nativeNapi insideNapi
      nativeWorker insideWorker Good) :
    Scheduler.Points.ChildContracts (schedulerPoints nativeConsume nativeNapi nativeWorker)
      (schedulerPoints insideConsume insideNapi insideWorker) Good :=
  Napi.Composition.schedulerChildren workGood
    (ReceiveWorker.Composition.napiChildren workGood acceptPeer
      (ReceiveWorker.Composition.stagedReceive acceptStaging receive))
    (ReceiveWorker.Composition.workerChildren workGood acceptPeer
      (ReceiveWorker.Composition.preparedWorkers workGood
        (ReceiveWorker.Composition.encryptionWorkers acceptEncryption workers)))

/-- Initialized runner service cuts inherit concrete encryption, staging,
timer, peer-release and send-drain proofs on their actual source paths. The
remaining four packet families, protocol sender and dispatch bodies are
named source assumptions, not an incoming conservation account. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (receive : ReceiveWorker.Composition.StagedReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good)
    (workers : ReceiveWorker.Composition.EncryptionWorkerOther nativeConsume insideConsume nativeNapi insideNapi
      nativeWorker insideWorker Good)
    (sender : ∀pid,WorkService.Points.ChildSourceContract (Expanded.workPoints nativeWork) (Expanded.workPoints insideWork)
      Good (.flushedSend pid))
    (dispatch : Composition.DispatchOther (servicePoints nativeConsume nativeNapi nativeWorker nativeWork)
      (servicePoints insideConsume insideNapi insideWorker insideWork) nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (RunnerCallbacks.runnerPoints (servicePoints nativeConsume nativeNapi nativeWorker nativeWork) nativeDispatch)
      Good (Runner.Points.executeShape trace placeholders) [] :=
  RunnerCallbacks.initialized trace placeholders carrierGood
    (Expanded.concreteChildren carrierGood workGood pendingGood acceptPeer acceptKeepalive
      (schedulerChildren workGood acceptPeer acceptStaging acceptEncryption receive workers) sender) dispatch

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.ReceiveComposition
