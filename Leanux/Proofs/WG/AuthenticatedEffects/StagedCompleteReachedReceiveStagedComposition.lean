import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingExpandedConsume
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceivePreparedComposition

/-! The initialized receive scheduler derives its expanded staging child.
Routed transmit, IPv6 receive and three worker bodies remain explicit source
contracts. Finer primitive interiors and universal caller coverage remain
separate obligations; this theorem does not declare T2 complete. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints} {Good : History → World → Prop}

structure StagedReceiveOther (nativeConsume insideConsume : Consume.Points.ChildPoints)
    (nativeNapi insideNapi : Napi.Points.ChildPoints) (Good : History → World → Prop) where
  transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract
    (napiPoints (StagingExpanded.consumePoints nativeConsume) nativeNapi)
    (napiPoints (StagingExpanded.consumePoints insideConsume) insideNapi) Good (.transmit family addr packets mtu)
  receive6 : ∀bytes,Napi.Points.ChildSourceContract
    (napiPoints (StagingExpanded.consumePoints nativeConsume) nativeNapi)
    (napiPoints (StagingExpanded.consumePoints insideConsume) insideNapi) Good (.receive6 bytes)

noncomputable def receiveStaging
    (accept : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (pid : PeerId) : Consume.Points.ChildSourceContract
      (WorkService.Composition.consumePoints (StagingExpanded.consumePoints nativeConsume))
      (WorkService.Composition.consumePoints (StagingExpanded.consumePoints insideConsume)) Good (.staging pid) where
  remainder:=StagingExpanded.rootRemainder pid
  continuation:=fun _ _ _ _ point=>StagingExpanded.root_remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before
    exact accept ledger middle u (StagingExpanded.RootPoint.evidence point account)

noncomputable def stagedReceive
    (accept : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (other : StagedReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good) :
    ReceiveOther (StagingExpanded.consumePoints nativeConsume) (StagingExpanded.consumePoints insideConsume)
      nativeNapi insideNapi Good where
  staging:=receiveStaging accept
  transmit:=other.transmit
  receive6:=other.receive6

/-- Initialized scheduler staging cuts conserve the original packet lineage,
including allocator aliases and pending disposal receipts, with no incoming
staging-source assumption. Five deeper packet families remain explicit. -/
theorem initialized_staged_scheduler
    (entry : ScheduledSource.Entry trace placeholders operationIndex world history)
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (receive : StagedReceiveOther nativeConsume insideConsume nativeNapi insideNapi Good)
    (workers : PreparedWorkerOther (StagingExpanded.consumePoints nativeConsume)
      (StagingExpanded.consumePoints insideConsume) nativeNapi insideNapi nativeWorker insideWorker Good) :
    Scheduler.Points.Covered
      (schedulerPoints (StagingExpanded.consumePoints nativeConsume) nativeNapi (Prepare.Points.iterationPoints nativeWorker)) Good
      (Scheduler.Points.scheduleShape none) world history ∧
    Scheduler.Points.Remainders
      (Napi.Composition.schedulerChildren carrierGood
        (napiChildren carrierGood acceptPeer (stagedReceive acceptStaging receive))
        (workerChildren carrierGood acceptPeer (preparedWorkers carrierGood workers)))
      (Scheduler.Points.scheduleShape none) world history :=
  initialized_prepared_scheduler entry carrierGood acceptPeer (stagedReceive acceptStaging receive) workers

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReceiveWorker.Composition
