import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveStagedComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionCallbackIteration

/-! The initialized receive scheduler supplies the fixed encryption callback
family, including its pending return receipt. Routed transmit, IPv6 receive,
peer transmit and handshake remain named contracts. Crypto primitive interiors
and universal native coverage are not claimed by this composition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints} {Good : History → World → Prop}

abbrev encryptionWorkerPoints (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  preparedWorkerPoints (StagingExpanded.consumePoints consume) napi
    (EncryptionCallback.iterationPoints other)

structure EncryptionWorkerOther (nativeConsume insideConsume : Consume.Points.ChildPoints)
    (nativeNapi insideNapi : Napi.Points.ChildPoints)
    (nativeWorker insideWorker : Iteration.Points.ChildPoints) (Good : History → World → Prop) where
  transmit : ∀pid,Iteration.Points.ChildSourceContract
    (encryptionWorkerPoints nativeConsume nativeNapi nativeWorker)
    (encryptionWorkerPoints insideConsume insideNapi insideWorker) Good (.transmit pid)
  handshake : Iteration.Points.ChildSourceContract
    (encryptionWorkerPoints nativeConsume nativeNapi nativeWorker)
    (encryptionWorkerPoints insideConsume insideNapi insideWorker) Good .handshake

noncomputable def workerEncryption
    (accept : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (item : Option (List SkbId)) : Iteration.Points.ChildSourceContract
      (encryptionWorkerPoints nativeConsume nativeNapi nativeWorker)
      (encryptionWorkerPoints insideConsume insideNapi insideWorker) Good (.encrypt item) where
  remainder:=EncryptionCallback.remainder item
  continuation:=fun _ _ _ _ point=>EncryptionCallback.remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before.1
    exact accept ledger middle u (EncryptionCallback.Point.evidence point account)

noncomputable def encryptionWorkers
    (accept : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (other : EncryptionWorkerOther nativeConsume insideConsume nativeNapi insideNapi nativeWorker insideWorker Good) :
    PreparedWorkerOther (StagingExpanded.consumePoints nativeConsume) (StagingExpanded.consumePoints insideConsume)
      nativeNapi insideNapi (EncryptionCallback.iterationPoints nativeWorker)
      (EncryptionCallback.iterationPoints insideWorker) Good where
  encrypt:=workerEncryption accept
  transmit:=other.transmit
  handshake:=other.handshake

/-- Initialized scheduler encryption cuts retain the admitted packet ledger,
the exact selected batch and its original continuation through byte writes,
publication, native peer release and the pending return receipt. Four deeper
packet contracts and finer primitive interiors remain explicit boundaries. -/
theorem initialized_encryption_scheduler
    (entry : ScheduledSource.Entry trace placeholders operationIndex world history)
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (receive : StagedReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good)
    (workers : EncryptionWorkerOther nativeConsume insideConsume nativeNapi insideNapi nativeWorker insideWorker Good) :
    Scheduler.Points.Covered
      (schedulerPoints (StagingExpanded.consumePoints nativeConsume) nativeNapi
        (Prepare.Points.iterationPoints (EncryptionCallback.iterationPoints nativeWorker))) Good
      (Scheduler.Points.scheduleShape none) world history ∧
    Scheduler.Points.Remainders
      (Napi.Composition.schedulerChildren carrierGood
        (napiChildren carrierGood acceptPeer (stagedReceive acceptStaging receive))
        (workerChildren carrierGood acceptPeer
          (preparedWorkers carrierGood (encryptionWorkers acceptEncryption workers))))
      (Scheduler.Points.scheduleShape none) world history :=
  initialized_staged_scheduler entry carrierGood acceptPeer acceptStaging receive
    (encryptionWorkers acceptEncryption workers)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
