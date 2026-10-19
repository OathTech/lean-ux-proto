import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageConfiguration
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Positional coverage crosses every actual syscall and the initialized native
trace runner. Every protected event has a current context; authorization of that
context remains a separate causal-root obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues Configuration
open HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem env_up : ProductAt frames (Driver.envUpObserved hooks) := by
  unfold Driver.envUpObserved
  repeat' first
    | (coverage_head Driver.upObserved; exact product_state _ up)
    | coverage_product_step

theorem env_down : ProductAt frames (Driver.envDownObserved hooks) := by
  unfold Driver.envDownObserved envDownWith
  repeat' first
    | (coverage_head Driver.downObserved; exact product_state _ down)
    | coverage_product_step

theorem env_delete : ProductAt frames (Driver.envDeleteObserved hooks) := by
  unfold Driver.envDeleteObserved HandshakeSecurity.SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (coverage_head Driver.downObserved; exact product_state _ down)
    | (coverage_head Driver.destructObserved; exact product_state _ destruct)
    | coverage_product_step

theorem socket_call (fd : Nat) (body : PrefixM Event Int) (safe : ProductAt frames body) :
    ProductAt frames (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  repeat' first | exact safe | coverage_product_step

theorem netlink (body : PrefixM Event Int) (safe : ProductAt frames body) :
    ProductAt frames (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  repeat' first
    | exact safe
    | (coverage_head socketCallOnWith; apply socket_call)
    | coverage_product_step

theorem rtnetlink (body : PrefixM Event Int) (safe : ProductAt frames body) :
    ProductAt frames (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact safe
    | (coverage_head socketCallOnWith; apply socket_call)
    | coverage_product_step

theorem retained (call : Syscall) : ProductAt frames (Driver.retainedObserved hooks call) := by
  cases call <;> unfold Driver.retainedObserved
  case wgUp => exact socket_call _ _ env_up
  case wgDown => exact socket_call _ _ env_down
  all_goals exact product_lift _

theorem observe : ProductAt frames (Driver.observeObserved hooks) :=
  product_bind idle_timers (fun _ => product_lift _)

theorem dispatch_observe : ProductAt frames (Driver.dispatchObserveObserved hooks) := by
  unfold Driver.dispatchObserveObserved
  repeat' first
    | (coverage_head Driver.observeObserved; exact observe)
    | (coverage_head socketCallOnWith; apply socket_call)
    | coverage_product_step

theorem dispatch (call : Syscall) : ProductAt frames (Driver.dispatchObserved hooks call) := by
  apply dispatchWith_preserves
  · exact fun call _ => retained call
  · intro attrs; exact netlink _ (product_state _ (config_device attrs))
  · exact rtnetlink _ (product_lift _)
  · exact rtnetlink _ env_delete
  · intro family addr payload opts; exact syscall_xmit family addr payload opts
  · intro family port msg tos ll dest
    exact socket_call _ _ (inject family port msg tos ll dest)
  · intro count port family messages; exact flood count port family messages
  · intro items; exact batch items
  · exact dispatch_observe

theorem syscall (call : Syscall) : ProductAt frames (Driver.syscallObserved hooks call) := by
  exact SyscallSource.preserves
    (I := fun h _ => Inv frames h)
    (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) call _ _ _ _ _ _ _
    (dispatch call) (send_workers) (idle_timers)
    (product_lift _) (after_xmit) (after_advance) (product_lift _)

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith
    (fun h _ => Inv [] h)
    Safe (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) (Driver.syscallObserved hooks)
    (fun call => syscall (frames := []) call) trace placeholders (fun _ _ => ⟨Safe.empty,rfl⟩)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
