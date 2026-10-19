import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeConfiguration
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Scope balance crosses every actual syscall and the initialized native trace
runner. These are history contracts; no memory or authentication premise is
inferred from the absence of malformed scope metadata. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues Configuration
open HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem env_up : ProductSafe (Driver.envUpObserved hooks) := by
  unfold Driver.envUpObserved
  repeat' first
    | (scope_balance_head Driver.upObserved; exact product_state _ up)
    | scope_product_step

theorem env_down : ProductSafe (Driver.envDownObserved hooks) := by
  unfold Driver.envDownObserved envDownWith
  repeat' first
    | (scope_balance_head Driver.downObserved; exact product_state _ down)
    | scope_product_step

theorem env_delete : ProductSafe (Driver.envDeleteObserved hooks) := by
  unfold Driver.envDeleteObserved HandshakeSecurity.SendExchange.envDeleteWith Configuration.envDeleteWith
  repeat' first
    | (scope_balance_head Driver.downObserved; exact product_state _ down)
    | (scope_balance_head Driver.destructObserved; exact product_state _ destruct)
    | scope_product_step

theorem socket_call (fd : Nat) (body : PrefixM Event Int) (safe : ProductSafe body) :
    ProductSafe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  repeat' first | exact safe | scope_product_step

theorem netlink (body : PrefixM Event Int) (safe : ProductSafe body) :
    ProductSafe (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  repeat' first
    | exact safe
    | (scope_balance_head socketCallOnWith; apply socket_call)
    | scope_product_step

theorem rtnetlink (body : PrefixM Event Int) (safe : ProductSafe body) :
    ProductSafe (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact safe
    | (scope_balance_head socketCallOnWith; apply socket_call)
    | scope_product_step

theorem retained (call : Syscall) : ProductSafe (Driver.retainedObserved hooks call) := by
  cases call <;> unfold Driver.retainedObserved
  case wgUp => exact socket_call _ _ env_up
  case wgDown => exact socket_call _ _ env_down
  all_goals exact product_lift _

theorem observe : ProductSafe (Driver.observeObserved hooks) :=
  product_bind idle_timers (fun _ => product_lift _)

theorem dispatch_observe : ProductSafe (Driver.dispatchObserveObserved hooks) := by
  unfold Driver.dispatchObserveObserved
  repeat' first
    | (scope_balance_head Driver.observeObserved; exact observe)
    | (scope_balance_head socketCallOnWith; apply socket_call)
    | scope_product_step

theorem dispatch (call : Syscall) : ProductSafe (Driver.dispatchObserved hooks call) := by
  intro frames
  apply dispatchWith_preserves
  · exact fun call _ => retained call frames
  · intro attrs; exact netlink _ (product_state _ (config_device attrs)) frames
  · exact rtnetlink _ (product_lift _) frames
  · exact rtnetlink _ env_delete frames
  · intro family addr payload opts; exact syscall_xmit family addr payload opts frames
  · intro family port msg tos ll dest
    exact socket_call _ _ (inject family port msg tos ll dest) frames
  · intro count port family messages; exact flood count port family messages frames
  · intro items; exact batch items frames
  · exact dispatch_observe frames

theorem syscall (call : Syscall) : ProductSafe (Driver.syscallObserved hooks call) := by
  intro frames
  exact SyscallSource.preserves
    (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
    (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
    (fun _ _ _ _ ready => ready) call _ _ _ _ _ _ _
    (dispatch call frames) (send_workers frames) (idle_timers frames)
    (product_lift _ frames) (after_xmit frames) (after_advance frames) (product_lift _ frames)

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    CausalScope.WellFormed scope? (runPrefixOuter (execute trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith
    (fun h _ => CausalScope.stack (h.filterMap scope?) = .ok [])
    (CausalScope.WellFormed scope?) (fun _ _ ready => ⟨[],ready⟩)
    (fun _ _ _ _ ready => ready) (Driver.syscallObserved hooks)
    (fun call => syscall call []) trace placeholders (fun _ _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
