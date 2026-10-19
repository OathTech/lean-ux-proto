import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointRunnerComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointScheduler

/-! A service scheduler call uses the same original scheduler source points
as committed worker scheduling. Its residual is constructed from that source
tree. Six other service families remain explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.SchedulerComposition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def servicePoints (scheduler : Scheduler.Points.ChildPoints) (other : Points.ChildPoints) :
    Points.ChildPoints := fun α action token w h u middle => match token with
  | .family (.schedule stack) => ∃site,Scheduler.Points.Point scheduler
      (Scheduler.Points.scheduleShape stack) w h site u middle
  | token => other α action token w h u middle

variable {native inside : Scheduler.Points.ChildPoints}
  {nativeOther insideOther : Points.ChildPoints} {Good : History → World → Prop}

noncomputable def remainder (stack : Option Worker)
    (children : Scheduler.Points.ChildContracts native inside Good)
    (w : World) (h : History) (u : World) (middle : History)
    (point : ∃site,Scheduler.Points.Point native (Scheduler.Points.scheduleShape stack) w h site u middle) :
    PrefixM Event Unit :=
  Classical.choose ((Classical.choose_spec point).residual children)

theorem remainder_run (stack : Option Worker)
    (children : Scheduler.Points.ChildContracts native inside Good)
    (point : ∃site,Scheduler.Points.Point native (Scheduler.Points.scheduleShape stack) w h site u middle) :
    runPrefix (Driver.scheduleObserved hooks stack) w h =
      runPrefix (remainder stack children w h u middle point) u middle :=
  (Classical.choose_spec ((Classical.choose_spec point).residual children)).run

noncomputable def schedule (stack : Option Worker)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Scheduler.Points.ChildContracts native inside Good) :
    Points.ChildSourceContract (servicePoints native nativeOther)
      (servicePoints inside insideOther) Good (.family (.schedule stack)) where
  remainder := remainder stack children
  continuation := fun _ _ _ _ point => remainder_run stack children point
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children before

structure OtherChildren (native inside : Scheduler.Points.ChildPoints)
    (nativeOther insideOther : Points.ChildPoints) (Good : History → World → Prop) where
  sends : Points.ChildSourceContract (servicePoints native nativeOther) (servicePoints inside insideOther) Good (.family .sends)
  sendWorker : Points.ChildSourceContract (servicePoints native nativeOther) (servicePoints inside insideOther) Good (.family .sendWorker)
  clearWorker : Points.ChildSourceContract (servicePoints native nativeOther) (servicePoints inside insideOther) Good (.family .clearWorker)
  timer : ∀pid timer,Points.ChildSourceContract (servicePoints native nativeOther) (servicePoints inside insideOther) Good (.family (.timer pid timer))
  selected : ∀device bound pid timer entry,Points.ChildSourceContract (servicePoints native nativeOther) (servicePoints inside insideOther) Good (.family (.selected device bound pid timer entry))
  finished : ∀token,Points.ChildSourceContract (servicePoints native nativeOther) (servicePoints inside insideOther) Good (.family (.finished token))

noncomputable def serviceChildren
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (scheduler : Scheduler.Points.ChildContracts native inside Good)
    (other : OtherChildren native inside nativeOther insideOther Good) :
    Points.ChildContracts (servicePoints native nativeOther) (servicePoints inside insideOther) Good where
  schedule := fun stack => schedule stack carrierGood scheduler
  sends := other.sends
  sendWorker := other.sendWorker
  clearWorker := other.clearWorker
  timer := other.timer
  selected := other.selected
  finished := other.finished

/-- Service scheduling now shares the concrete NAPI, committed iteration and
peer-release construction. Only their named remaining packet families and
the other six service families are supplied as child contracts. -/
noncomputable def serviceWorkerChildren
    {nativeNapi insideNapi : Napi.Points.ChildPoints}
    {nativeWorker insideWorker : Iteration.Points.ChildPoints}
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (napi : PeerRetirement.Points.NapiOther nativeNapi insideNapi Good)
    (workers : PeerRetirement.Points.WorkerOther nativeNapi insideNapi nativeWorker insideWorker Good)
    (other : OtherChildren (PeerRetirement.Points.schedulerPoints nativeNapi nativeWorker)
      (PeerRetirement.Points.schedulerPoints insideNapi insideWorker) nativeOther insideOther Good) :
    Points.ChildContracts
      (servicePoints (PeerRetirement.Points.schedulerPoints nativeNapi nativeWorker) nativeOther)
      (servicePoints (PeerRetirement.Points.schedulerPoints insideNapi insideWorker) insideOther) Good :=
  serviceChildren (fun h w before => carrierGood h w before.1)
    (Napi.Composition.schedulerChildren carrierGood
      (PeerRetirement.Points.napiChildren accept napi) (PeerRetirement.Points.workerChildren accept workers)) other

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.SchedulerComposition
