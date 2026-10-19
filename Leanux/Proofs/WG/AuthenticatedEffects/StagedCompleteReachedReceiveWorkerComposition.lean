import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCryptPollPointIteration
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointPeerComposition

/-! Shared receive, queued-work, ring-poll and peer-release instances fill
the original committed scheduler graph. Seven distinct deeper packet families
remain explicit; no initialized native-completeness claim is made yet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def napiPoints (consume : Consume.Points.ChildPoints) (other : Napi.Points.ChildPoints) :
    Napi.Points.ChildPoints :=
  Consume.Points.napiPoints (WorkService.Composition.consumePoints consume)
    (PeerRetirement.Points.napiPoints other)

def baseWorkerPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  CryptPoll.Composition.iterationPoints (PeerRetirement.Points.iterationPoints other)

def workerPoints (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  Napi.Composition.iterationPoints (napiPoints consume napi) (baseWorkerPoints other)

def schedulerPoints (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (other : Iteration.Points.ChildPoints) : Scheduler.Points.ChildPoints :=
  Napi.Composition.schedulerPoints (napiPoints consume napi) (baseWorkerPoints other)

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints} {Good : History → World → Prop}

structure ReceiveOther (nativeConsume insideConsume : Consume.Points.ChildPoints)
    (nativeNapi insideNapi : Napi.Points.ChildPoints) (Good : History → World → Prop) where
  staging : ∀pid,Consume.Points.ChildSourceContract
    (WorkService.Composition.consumePoints nativeConsume) (WorkService.Composition.consumePoints insideConsume) Good (.staging pid)
  transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract
    (napiPoints nativeConsume nativeNapi) (napiPoints insideConsume insideNapi) Good (.transmit family addr packets mtu)
  receive6 : ∀bytes,Napi.Points.ChildSourceContract
    (napiPoints nativeConsume nativeNapi) (napiPoints insideConsume insideNapi) Good (.receive6 bytes)

noncomputable def napiRelease
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option PeerId) : Napi.Points.ChildSourceContract
      (napiPoints nativeConsume nativeNapi) (napiPoints insideConsume insideNapi) Good (.release peer) where
  remainder := fun _ _ _ _ point => PeerRetirement.Points.continuation point
  continuation := fun _ _ _ _ point => PeerRetirement.Points.continuation_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before
    exact accept ledger middle u (PeerRetirement.Points.native_evidence accounted point)

noncomputable def napiChildren
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (other : ReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good) :
    Napi.Points.ChildContracts (napiPoints nativeConsume nativeNapi) (napiPoints insideConsume insideNapi) Good :=
  Consume.Points.napi_children carrierGood
    (WorkService.Composition.consumeChildren carrierGood accept other.staging)
    (napiRelease accept) other.transmit other.receive6

structure WorkerOther (nativeConsume insideConsume : Consume.Points.ChildPoints)
    (nativeNapi insideNapi : Napi.Points.ChildPoints)
    (nativeWorker insideWorker : Iteration.Points.ChildPoints) (Good : History → World → Prop) where
  encrypt : ∀item,Iteration.Points.ChildSourceContract
    (workerPoints nativeConsume nativeNapi nativeWorker) (workerPoints insideConsume insideNapi insideWorker) Good (.encrypt item)
  transmit : ∀pid,Iteration.Points.ChildSourceContract
    (workerPoints nativeConsume nativeNapi nativeWorker) (workerPoints insideConsume insideNapi insideWorker) Good (.transmit pid)
  prepare : Iteration.Points.ChildSourceContract
    (workerPoints nativeConsume nativeNapi nativeWorker) (workerPoints insideConsume insideNapi insideWorker) Good .prepare
  handshake : Iteration.Points.ChildSourceContract
    (workerPoints nativeConsume nativeNapi nativeWorker) (workerPoints insideConsume insideNapi insideWorker) Good .handshake

noncomputable def workerPoll
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w) :
    Iteration.Points.ChildSourceContract (workerPoints nativeConsume nativeNapi nativeWorker)
      (workerPoints insideConsume insideNapi insideWorker) Good .poll where
  remainder := CryptPoll.Points.remainder
  continuation := fun _ _ _ _ point => CryptPoll.Points.remainder_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before.1
    exact carrierGood middle u ⟨ledger,(CryptPoll.Points.source_accounted accounted point).1⟩

noncomputable def workerRelease
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (pid : PeerId) : Iteration.Points.ChildSourceContract
      (workerPoints nativeConsume nativeNapi nativeWorker)
      (workerPoints insideConsume insideNapi insideWorker) Good (.release pid) where
  remainder := fun _ _ _ _ point => PeerRetirement.Points.continuation point
  continuation := fun _ _ _ _ point => PeerRetirement.Points.continuation_run point
  coverage := fun _ _ _ _ point => point
  safe := by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before.1
    exact accept ledger middle u (PeerRetirement.Points.native_evidence accounted point)

noncomputable def workerChildren
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (other : WorkerOther nativeConsume insideConsume nativeNapi insideNapi nativeWorker insideWorker Good) :
    Napi.Composition.OtherChildren (napiPoints nativeConsume nativeNapi) (napiPoints insideConsume insideNapi)
      (baseWorkerPoints nativeWorker) (baseWorkerPoints insideWorker) Good where
  poll := workerPoll carrierGood
  release := workerRelease accept
  encrypt := other.encrypt
  transmit := other.transmit
  prepare := other.prepare
  handshake := other.handshake

/-- Initialized scheduler points share the concrete receive, queued-initiation,
wheel, ring-poll and release proofs. Seven deeper source contracts remain
explicit; no input packet account is assumed at initialization. -/
theorem initialized_scheduler
    (entry : ScheduledSource.Entry trace placeholders operationIndex world history)
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (receive : ReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good)
    (workers : WorkerOther nativeConsume insideConsume nativeNapi insideNapi nativeWorker insideWorker Good) :
    Scheduler.Points.Covered (schedulerPoints nativeConsume nativeNapi nativeWorker) Good
      (Scheduler.Points.scheduleShape none) world history ∧
    Scheduler.Points.Remainders
      (Napi.Composition.schedulerChildren carrierGood (napiChildren carrierGood accept receive)
        (workerChildren carrierGood accept workers)) (Scheduler.Points.scheduleShape none) world history :=
  Napi.Composition.initialized_source entry carrierGood (napiChildren carrierGood accept receive)
    (workerChildren carrierGood accept workers)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
