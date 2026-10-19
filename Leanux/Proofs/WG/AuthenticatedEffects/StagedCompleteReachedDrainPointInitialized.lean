import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendInitialized

/-! Initialized send-drain points inherit their actual entry account from
the original runner. Child coverage remains an explicit source obligation;
the continuation bridge cannot manufacture an interior source point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
variable {native inside : SendDrain.Points.ChildPoints} {Good : List Event → World → Prop}

theorem Entry.points
    (entry : Entry trace placeholders operationIndex world history)
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : SendDrain.Points.ChildContracts native inside Good) :
    SendDrain.Points.Covered native Good world history :=
  SendDrain.Points.native_covered carrierGood children entry.carrier

theorem Entry.child_continuation
    (entry : Entry trace placeholders operationIndex world history)
    (path : SendDrain.Points.ChildEntry world history child u middle)
    (children : SendDrain.Points.ChildContracts native inside Good)
    (point : native child u middle v last) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume v (children.remainder point >>= fun _ => path.after)) last := by
  rw [entry.original]
  exact entry.resume_run_eq _ _ (path.interior_continuation children point)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendRun
