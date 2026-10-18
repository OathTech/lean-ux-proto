import Leanux.Proofs.WG.Roaming.RemoteDriverControlsSource
import Leanux.Proofs.WG.Roaming.RemoteDriverDispatchTrafficSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Dispatch
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def call (c : Syscall) : PrefixM Event Int :=
  dispatchWith (fun c=>focus (RxHistory.syscallDispatch c)) Outer.set Outer.create Outer.delete
    Outer.xmit Outer.inject Traffic.flood Traffic.batch Outer.observe c

theorem call_preserves (entry : RemoteMap) (c : Syscall) :
    PrefixPreserves (Inv entry) Safe (call c) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _
    (RemoteDispatch.retained_covered entry) (Outer.set_preserves entry)
    (Outer.create_preserves entry) (Outer.delete_preserves entry) (Outer.xmit_preserves entry)
    (Outer.inject_preserves entry) (Traffic.flood_preserves entry) (Traffic.batch_preserves entry)
    (Outer.observe_preserves entry) c

theorem call_projects (c : Syscall) :
    ProjectsPrefix rxEvent id (call c) (RxHistory.syscallDispatch c) := by
  rw [rxDispatch_source]
  exact dispatchWith_projects _ _ _ _ _ _ _ _ _ rxEvent _ _ _ _ _ _ _ _ _
    (fun c _=>Scheduler.focus_projects _ (RxHistory.syscallDispatch_appends c))
    Outer.set_projects Outer.create_projects Outer.delete_projects Outer.xmit_projects
    Outer.inject_projects Traffic.flood_projects Traffic.batch_projects Outer.observe_projects c

theorem call_appends (c : Syscall) : Appends (call c) := by
  cases c
  case wgSet attrs => exact Outer.set_appends attrs
  case wgCreate => exact Outer.create_appends
  case wgDelete => exact Outer.delete_appends
  case wgXmit family addr payload opts => exact Outer.xmit_appends family addr payload opts
  case wgInject family port msg tos ll dest => exact Outer.inject_appends family port msg tos ll dest
  case wgFlood count port family msgs => exact Traffic.flood_appends count port family msgs
  case wgBatch items _ => exact Traffic.batch_appends items
  case wgObserve => exact Outer.observe_appends
  all_goals exact Appends.focus _ _ _

theorem call_erases (c : Syscall) : ErasesPrefix (call c) (Leanux.dispatch c) :=
  projection_erases (call_projects c) (RxHistory.syscallDispatch_erases c)

end Leanux.Proofs.WG.Roaming.RemoteDriver.Dispatch
