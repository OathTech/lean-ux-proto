import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveWorkerComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointIteration

/-! The initialized receive scheduler now derives its preparation child.
The three remaining worker families and three receive families stay named;
the earlier seven-contract composition retains its original statement. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

abbrev preparedWorkerPoints (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  workerPoints consume napi (Prepare.Points.iterationPoints other)

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints} {Good : History → World → Prop}

structure PreparedWorkerOther (nativeConsume insideConsume : Consume.Points.ChildPoints)
    (nativeNapi insideNapi : Napi.Points.ChildPoints)
    (nativeWorker insideWorker : Iteration.Points.ChildPoints) (Good : History → World → Prop) where
  encrypt : ∀item,Iteration.Points.ChildSourceContract
    (preparedWorkerPoints nativeConsume nativeNapi nativeWorker)
    (preparedWorkerPoints insideConsume insideNapi insideWorker) Good (.encrypt item)
  transmit : ∀pid,Iteration.Points.ChildSourceContract
    (preparedWorkerPoints nativeConsume nativeNapi nativeWorker)
    (preparedWorkerPoints insideConsume insideNapi insideWorker) Good (.transmit pid)
  handshake : Iteration.Points.ChildSourceContract
    (preparedWorkerPoints nativeConsume nativeNapi nativeWorker)
    (preparedWorkerPoints insideConsume insideNapi insideWorker) Good .handshake

noncomputable def workerPrepare
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w) :
    Iteration.Points.ChildSourceContract
      (preparedWorkerPoints nativeConsume nativeNapi nativeWorker)
      (preparedWorkerPoints insideConsume insideNapi insideWorker) Good .prepare where
  remainder:=Prepare.Points.remainder
  continuation:=fun _ _ _ _ point=>Prepare.Points.remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩:=before.1
    exact carrierGood middle u ⟨ledger,Prepare.Points.RootPoint.accounted accounted point⟩

noncomputable def preparedWorkers
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (other : PreparedWorkerOther nativeConsume insideConsume nativeNapi insideNapi nativeWorker insideWorker Good) :
    WorkerOther nativeConsume insideConsume nativeNapi insideNapi
      (Prepare.Points.iterationPoints nativeWorker) (Prepare.Points.iterationPoints insideWorker) Good where
  encrypt:=other.encrypt
  transmit:=other.transmit
  prepare:=workerPrepare carrierGood
  handshake:=other.handshake

/-- Initialized scheduler preparation points conserve the original packet
ledger and continuation without a preparation-source assumption. Six deeper
packet families remain explicit; this is not global native-cut completion. -/
theorem initialized_prepared_scheduler
    (entry : ScheduledSource.Entry trace placeholders operationIndex world history)
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (receive : ReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good)
    (workers : PreparedWorkerOther nativeConsume insideConsume nativeNapi insideNapi nativeWorker insideWorker Good) :
    Scheduler.Points.Covered
      (schedulerPoints nativeConsume nativeNapi (Prepare.Points.iterationPoints nativeWorker)) Good
      (Scheduler.Points.scheduleShape none) world history ∧
    Scheduler.Points.Remainders
      (Napi.Composition.schedulerChildren carrierGood (napiChildren carrierGood accept receive)
        (workerChildren carrierGood accept (preparedWorkers carrierGood workers)))
      (Scheduler.Points.scheduleShape none) world history :=
  initialized_scheduler entry carrierGood accept receive (preparedWorkers carrierGood workers)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
