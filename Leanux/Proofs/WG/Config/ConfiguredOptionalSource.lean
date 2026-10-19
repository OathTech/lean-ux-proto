import Leanux.Proofs.WG.Config.ConfiguredBoundaryBridge
import Leanux.Proofs.WG.AllowedIps.RoutingInitial
import Leanux.Proofs.WG.AllowedIps.RoutingEnvTrafficFrames
import Leanux.Proofs.WG.Queues.BaseCoherenceCalls
import Leanux.Proofs.WG.AllowedIps.RoutingEnvControlsCompletion

import Leanux.Proofs.WG.Config.ConfiguredOptionalEffects
import Leanux.Proofs.WG.Config.ConfiguredOptionalFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem optionalReady_native {α : Type} (action : WG.M α)
    (routing : RetainsRoutingCall action)
    (base : SameView BaseCoherence.view action) :
    Preserves OptionalReady action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result v b pre run
  apply optionalReady_retains g v
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp routing g a result v b run
  · exact congrArg Prod.fst
      ((ProjectedAction.iff_run_ambient _ _ _).mp base g a result v b run)
  · exact pre

theorem optionalReady_product {α : Type} (action : Leanux.M α)
    (routing : ProjectedRetainsRoutingCall World.wg action)
    (base : SameView (fun w : World => BaseCoherence.view w.wg) action) :
    Preserves (fun w => OptionalReady w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  apply optionalReady_retains w.wg v.wg
  · exact (ProjectedAction.iff_run _ _ _).mp routing w result v run
  · exact congrArg Prod.fst ((ProjectedAction.iff_run _ _ _).mp base w result v run)
  · exact pre

theorem optionalReady_inject (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves (fun w => OptionalReady w.wg) (Env.inject family port msg tos ll dest) :=
  optionalReady_product _ (inject_routing family port msg tos ll dest)
    (base_frame_from_prefix _ _ (RxHistory.inject_erases family port msg tos ll dest)
      (fun initial => BaseCoherence.inject_structure initial family port msg tos ll dest))

theorem optionalReady_flood (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (fun w => OptionalReady w.wg) (Env.flood count port family messages) :=
  optionalReady_product _ (flood_routing count port family messages)
    (base_frame_from_prefix _ _ (RxHistory.flood_erases count port family messages)
      (fun initial => BaseCoherence.flood_structure initial count port family messages))

theorem optionalReady_batch (items : List Env.BatchItem) :
    Preserves (fun w => OptionalReady w.wg) (Env.batch items) :=
  optionalReady_product _ (batch_routing items)
    (base_frame_from_prefix _ _ (RxHistory.batch_erases items)
      (fun initial => BaseCoherence.batch_structure initial items))

theorem optionalReady_schedule (stack : Option Worker) :
    Preserves (fun w => OptionalReady w.wg) (Env.schedule stack) :=
  optionalReady_product _ (schedule_routing stack)
    (base_frame_from_prefix _ _ (RxHistory.schedule_erases stack)
      (fun initial => BaseCoherence.schedule_structure initial stack))

theorem optionalReady_dispatch (worker : Worker) :
    Preserves (fun w => OptionalReady w.wg) (Env.dispatch worker) :=
  optionalReady_product _ (dispatch_routing worker)
    (base_frame_from_prefix _ _ (RxHistory.dispatch_erases worker)
      (fun initial => BaseCoherence.dispatch_structure initial worker))

theorem optionalReady_deferred (call : EnvDeferredCall) :
    Preserves (fun w => OptionalReady w.wg) call.original := by
  have routing : ProjectedRetainsRoutingCall World.wg call.original := by
    cases call with
    | drained what queues => exact ProjectedRetainsRoutingCall.of_same (requireDrained_routing what queues)
    | idleDevice => exact ProjectedRetainsRoutingCall.of_same requireIdleDevice_routing
    | noCrypt => exact ProjectedRetainsRoutingCall.of_same requireNoCryptWork_routing
    | crypt => exact runCryptWorkers_routing
    | sendOne => exact runOneSendWorker_routing
    | clearOne => exact runOneClearWorker_routing
    | sendAll => exact runSendWorkers_routing
    | afterXmit => exact afterXmit_routing
    | timerWorker timer =>
      exact ProjectedRetainsRoutingCall.of_same ((timerWorker_sameKernel timer).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl))
    | timers jHi => exact runTimers_routing jHi
    | placeholder jHi => exact runTimersPlaceholder_routing jHi
    | idle => exact idleTimers_routing
    | advance ticks => exact ProjectedRetainsRoutingCall.of_same (advance_routing ticks)
    | afterAdvance => exact afterAdvance_routing
  exact optionalReady_product _ routing
    (base_frame_from_prefix _ _ (RxHistory.deferred_erases call)
      (fun initial => BaseCoherence.deferred_structure initial call))

end Leanux.Proofs.WG.Config.OwnerConfiguration
