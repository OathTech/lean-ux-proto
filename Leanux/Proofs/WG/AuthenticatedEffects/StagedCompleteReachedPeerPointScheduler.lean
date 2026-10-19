import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointInitialized

/-! Concrete peer release is shared by NAPI and the committed worker
iteration. Remaining source contracts are named only for other families. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal
variable {native inside : Napi.Points.ChildPoints}
  {nativeOther insideOther : Iteration.Points.ChildPoints} {G : History → World → Prop}

structure NapiOther (native inside : Napi.Points.ChildPoints) (G : History → World → Prop) where
  counter : ∀skb packet,Napi.Points.ChildSourceContract (napiPoints native) (napiPoints inside) G (.counter skb packet)
  consume : ∀pid packet endpoint,Napi.Points.ChildSourceContract (napiPoints native) (napiPoints inside) G (.consume pid packet endpoint)
  transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract (napiPoints native) (napiPoints inside) G (.transmit family addr packets mtu)
  receive6 : ∀bytes,Napi.Points.ChildSourceContract (napiPoints native) (napiPoints inside) G (.receive6 bytes)

noncomputable def napiChildren
    (accept : ∀ledger h w,Evidence ledger [] [] h w.wg→G h w)
    (other : NapiOther native inside G) :
    Napi.Points.ChildContracts (napiPoints native) (napiPoints inside) G where
  counter:=other.counter
  consume:=other.consume
  release:=napiRelease accept native inside
  transmit:=other.transmit
  receive6:=other.receive6

def workerPoints (napi : Napi.Points.ChildPoints) (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  Napi.Composition.iterationPoints (napiPoints napi) (iterationPoints other)

def schedulerPoints (napi : Napi.Points.ChildPoints) (other : Iteration.Points.ChildPoints) : Scheduler.Points.ChildPoints :=
  Napi.Composition.schedulerPoints (napiPoints napi) (iterationPoints other)

structure WorkerOther (native inside : Napi.Points.ChildPoints)
    (nativeOther insideOther : Iteration.Points.ChildPoints) (G : History → World → Prop) where
  poll : Iteration.Points.ChildSourceContract (workerPoints native nativeOther) (workerPoints inside insideOther) G .poll
  encrypt : ∀item,Iteration.Points.ChildSourceContract (workerPoints native nativeOther) (workerPoints inside insideOther) G (.encrypt item)
  transmit : ∀pid,Iteration.Points.ChildSourceContract (workerPoints native nativeOther) (workerPoints inside insideOther) G (.transmit pid)
  prepare : Iteration.Points.ChildSourceContract (workerPoints native nativeOther) (workerPoints inside insideOther) G .prepare
  handshake : Iteration.Points.ChildSourceContract (workerPoints native nativeOther) (workerPoints inside insideOther) G .handshake

noncomputable def workerRelease
    (accept : ∀ledger h w,Evidence ledger [] [] h w.wg→G h w)
    (native inside : Napi.Points.ChildPoints) (nativeOther insideOther : Iteration.Points.ChildPoints)
    (pid : PeerId) :
    Iteration.Points.ChildSourceContract (workerPoints native nativeOther) (workerPoints inside insideOther) G (.release pid) where
  remainder:=fun _ _ _ _ point=>continuation point
  continuation:=fun _ _ _ _ point=>continuation_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩ := before.1
    exact accept ledger middle u (native_evidence accounted point)

noncomputable def workerChildren
    (accept : ∀ledger h w,Evidence ledger [] [] h w.wg→G h w)
    (other : WorkerOther native inside nativeOther insideOther G) :
    Napi.Composition.OtherChildren (napiPoints native) (napiPoints inside)
      (iterationPoints nativeOther) (iterationPoints insideOther) G where
  poll:=other.poll
  encrypt:=other.encrypt
  transmit:=other.transmit
  prepare:=other.prepare
  release:=workerRelease accept native inside nativeOther insideOther
  handshake:=other.handshake

/-- Initialized scheduler coverage has concrete release, NAPI and iteration
composition. Its nine remaining deeper source families remain explicit. -/
theorem initialized_scheduler
    (entry : ScheduledSource.Entry trace placeholders operationIndex world history)
    (carrierGood : ∀h w,Napi.Points.Carrier h w→G h w)
    (accept : ∀ledger h w,Evidence ledger [] [] h w.wg→G h w)
    (napi : NapiOther native inside G)
    (workers : WorkerOther native inside nativeOther insideOther G) :
    Scheduler.Points.Covered (schedulerPoints native nativeOther) G
      (Scheduler.Points.scheduleShape none) world history ∧
    Scheduler.Points.Remainders
      (Napi.Composition.schedulerChildren carrierGood (napiChildren accept napi) (workerChildren accept workers))
      (Scheduler.Points.scheduleShape none) world history :=
  Napi.Composition.initialized_source entry carrierGood (napiChildren accept napi) (workerChildren accept workers)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
