import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointInitialized

/-! Canonical NAPI fills all three actual scheduler/iteration NAPI calls.
The remaining six iteration families and five NAPI families are named once;
this composition introduces no recursive assumption about its own callers. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Composition
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev ChildPoints := Napi.Points.ChildPoints
abbrev OtherPoints := Iteration.Points.ChildPoints
abbrev History := List Event

def napiPoints (inside : ChildPoints) : Iteration.Points.NapiPoints :=
  fun w h u middle=>∃site,Napi.Points.Point inside Napi.Points.softirqShape w h site u middle

def iterationPoints (inside : ChildPoints) (other : OtherPoints) : OtherPoints :=
  Napi.Points.iterationPoints inside other

def schedulerPoints (inside : ChildPoints) (other : OtherPoints) : Scheduler.Points.ChildPoints :=
  Iteration.Points.schedulerPoints (iterationPoints inside other) (napiPoints inside)

variable {native inside : ChildPoints} {nativeOther insideOther : OtherPoints}
  {Good : History → World → Prop}

structure OtherChildren (native inside : ChildPoints) (nativeOther insideOther : OtherPoints)
    (Good : History → World → Prop) where
  poll : Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
    (iterationPoints inside insideOther) Good .poll
  encrypt : ∀item,Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
    (iterationPoints inside insideOther) Good (.encrypt item)
  transmit : ∀pid,Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
    (iterationPoints inside insideOther) Good (.transmit pid)
  prepare : Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
    (iterationPoints inside insideOther) Good .prepare
  release : ∀pid,Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
    (iterationPoints inside insideOther) Good (.release pid)
  handshake : Iteration.Points.ChildSourceContract (iterationPoints native nativeOther)
    (iterationPoints inside insideOther) Good .handshake

noncomputable def iterationChildren
    (carrierGood : ∀h w,Napi.Points.Carrier h w→Good h w)
    (children : Napi.Points.ChildContracts native inside Good)
    (other : OtherChildren native inside nativeOther insideOther Good) :
    Iteration.Points.ChildContracts (iterationPoints native nativeOther)
      (iterationPoints inside insideOther) Good where
  poll:=other.poll
  encrypt:=other.encrypt
  transmit:=other.transmit
  prepare:=other.prepare
  release:=other.release
  handshake:=other.handshake
  softirq:=Napi.Points.iteration_softirq carrierGood children
  irqExit:=Napi.Points.iteration_irq carrierGood children

noncomputable def schedulerChildren
    (carrierGood : ∀h w,Napi.Points.Carrier h w→Good h w)
    (children : Napi.Points.ChildContracts native inside Good)
    (other : OtherChildren native inside nativeOther insideOther Good) :
    Scheduler.Points.ChildContracts (schedulerPoints native nativeOther)
      (schedulerPoints inside insideOther) Good :=
  Iteration.Points.scheduler_children (fun h w before=>carrierGood h w before.1)
    (iterationChildren carrierGood children other)
    (Napi.Points.scheduler_napi carrierGood children)

/-- Initialized scheduling now structurally covers its committed iteration
and NAPI calls, with the exact finite deeper contracts still visible. -/
theorem initialized_source
    (entry : ScheduledSource.Entry trace placeholders operationIndex world history)
    (carrierGood : ∀h w,Napi.Points.Carrier h w→Good h w)
    (children : Napi.Points.ChildContracts native inside Good)
    (other : OtherChildren native inside nativeOther insideOther Good) :
    Scheduler.Points.Covered (schedulerPoints native nativeOther) Good
      (Scheduler.Points.scheduleShape none) world history ∧
      Scheduler.Points.Remainders (schedulerChildren carrierGood children other)
        (Scheduler.Points.scheduleShape none) world history :=
  entry.source_points (fun h w before=>carrierGood h w before.1)
    (schedulerChildren carrierGood children other)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Composition
