import Leanux.Proofs.WG.Origins.ShapedRunnerInvariant
import Leanux.Proofs.WG.Configuration.RoutingSyscalls
import Leanux.Proofs.WG.Configuration.InitializedJoint

/-! Positional routing on the actual initialized joint journal. Shape is
required only for operations in the trace. Both placeholder modes and every
indexed Stop retain the routing checks at each captured consume entry. -/
namespace Leanux.Proofs.WG.RoutingPosition.Runner
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps Configuration

private theorem store (h : List RoutingJoint.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Inv initial h w) :
    Inv initial h v := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  exact ⟨by simpa only [GlobalCompletionState,routingView,device] using hi.1,hi.2⟩

private theorem identity (g : PrefixM RoutingJoint.Event α) :
    ProjectsPrefix some id g g := by
  intro w h
  simp only [List.filterMap_some]
  cases runPrefix g w h with
  | mk result hist => cases result <;> rfl

/-- Removing only the final World result leaves the identical joint journal
and indexed Stop, for every incoming history. -/
theorem executeTrace_sameJournal (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    ProjectsOuter some Prod.fst (RoutingJoint.executeTrace trace placeholders)
      (RxHistory.executeTraceWith RoutingJoint.syscall trace placeholders) := by
  rw [RoutingJoint.executeTrace_rx_factor]
  exact RoutingJoint.executeTraceWith_projects some Prod.fst
    RoutingJoint.syscall RoutingJoint.syscall (fun j v => (j,v)) (fun j _ => j)
    (fun c => identity _) (fun _ _ => rfl) trace placeholders

/-- The current semantic routing table and every strict-prefix consume check
come from the original fixture and actual shaped trace, including Stop prefixes.
No publication, delivery or authorization fact is an input. -/
theorem executeTrace (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace)
    (placeholders : Bool) :
    Safe ([],[]) (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 := by
  have checked := RunnerInvariant.Shaped.executeTraceWith (Inv ([],[])) (Safe ([],[]))
    (fun _ _ hi => hi.safe) store SyscallAddressShape RoutingJoint.syscall
    (Calls.syscall ([],[])) trace
    (fun op member results ends index => toSyscall_shape results ends index op (shape op member))
    placeholders (inv_initial trace)
  have journal := congrArg Prod.snd (executeTrace_sameJournal trace placeholders [])
  simp only [List.filterMap_nil,List.filterMap_some] at journal
  rwa [journal] at checked

end Leanux.Proofs.WG.RoutingPosition.Runner
