import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryTraffic
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryConfiguration
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! One generic initialized native-runner history theorem. Every hook contract
is explicit; no state-dependent security invariant is hidden in this interface. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

namespace History

theorem socketCall (fd : Nat) (body : PrefixM E Int) (hb : ProductHistorySafe Safe body) :
    ProductHistorySafe Safe (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  repeat' first | exact hb | driver_product_history_step

theorem netlink (body : PrefixM E Int) (hb : ProductHistorySafe Safe body) :
    ProductHistorySafe Safe (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  repeat' first
    | exact hb
    | (driver_history_head socketCallOnWith; apply socketCall)
    | driver_product_history_step

theorem rtnetlink (body : PrefixM E Int) (hb : ProductHistorySafe Safe body) :
    ProductHistorySafe Safe (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (driver_history_head socketCallOnWith; apply socketCall)
    | driver_product_history_step

end History

theorem retained_history (h : HooksHistorySafe Safe g) (call : Syscall) :
    ProductHistorySafe Safe (retainedObserved g call) := by
  cases call <;> unfold retainedObserved
  case wgUp => exact History.socketCall _ _ (envUp_history h)
  all_goals exact History.product_lift _

theorem observe_history (h : HooksHistorySafe Safe g) :
    ProductHistorySafe Safe (observeObserved g) :=
  History.product_bind (idleTimers_history h) (fun _ => History.product_lift _)

theorem dispatchObserve_history (h : HooksHistorySafe Safe g) :
    ProductHistorySafe Safe (dispatchObserveObserved g) := by
  unfold dispatchObserveObserved
  apply History.product_bind (observe_history h)
  rintro ⟨ret, json⟩
  dsimp only
  apply History.product_bind (History.product_lift _)
  intro _
  exact History.socketCall _ _ (History.product_pure ret)

theorem dispatchSet_history (h : HooksHistorySafe Safe g) (attrs : DeviceAttrs) :
    ProductHistorySafe Safe (dispatchSetObserved g attrs) :=
  History.netlink _ ((configDevice_history h attrs).liftWGObserver)

theorem dispatchCreate_history : ProductHistorySafe Safe dispatchCreateObserved :=
  History.rtnetlink _ (History.product_lift _)

theorem dispatchDelete_history : ProductHistorySafe Safe dispatchDeleteObserved :=
  History.rtnetlink _ (History.product_lift _)

theorem dispatch_history (h : HooksHistorySafe Safe g) (call : Syscall) :
    ProductHistorySafe Safe (dispatchObserved g call) := by
  apply dispatchWith_preserves
  · exact fun call _ => retained_history h call
  · exact dispatchSet_history h
  · exact dispatchCreate_history
  · exact dispatchDelete_history
  · exact syscallXmit_history h
  · intro family port message tos ll dest
    exact History.socketCall _ _ (inject_history h family port message tos ll dest)
  · exact flood_history h
  · exact batch_history h
  · exact dispatchObserve_history h

theorem syscall_history (h : HooksHistorySafe Safe g) (call : Syscall) :
    ProductHistorySafe Safe (syscallObserved g call) :=
  SyscallSource.preserves (I := fun h _ => Safe h) (S := Safe)
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) call _ _ _ _ _ _ _
    (dispatch_history h call) (sendWorkers_history h) (idleTimers_history h)
    (History.product_lift _) (afterXmit_history h) (afterAdvance_history h) (History.product_lift _)

/-- Safe hook histories remain safe through every typed original runner trace,
including its indexed Stop, both timer modes, and the original initialization. -/
theorem initialized_history (h : HooksHistorySafe Safe g) (empty : Safe [])
    (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (executeObserved g trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith (fun h _ => Safe h) Safe
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) (syscallObserved g)
    (syscall_history h) trace placeholders (fun _ _ => empty)

end Leanux.Proofs.WG.TransmitSecurity.Driver
