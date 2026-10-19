import Leanux.Proofs.WG.HandshakeSecurity.DriverDeliveryNeutral
import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionDispatchFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration TransmitSecurity

open Responder.DriverCuts (hooks)

/-- Named native effects needed by the actual full driver. The package contains
no history, initialization, reachability or uniqueness conclusion. -/
structure H1DriverFrames : Prop where
  deferred : H1DeferredFrames
  ingress : H1IngressFrames
  configuration : H1ConfigurationFrames
  lifecycle : H1LifecycleFrames

theorem retained_dispatch (facts : H1DriverFrames) (call : Syscall)
    (retained : DispatchRetained call) : ProductPreserves (Driver.retainedObserved hooks call) := by
  by_cases up : call = .wgUp
  · subst call
    exact Outer.socketCallOn _ _ (env_up facts.deferred)
  · have native : Driver.retainedObserved hooks call = liftPrefix (Leanux.dispatch call) := by
      cases call <;> unfold Driver.retainedObserved
      case wgUp => exact False.elim (up rfl)
      case wgDown =>
        rw [Driver.envDown_lift hooks rfl rfl rfl,Driver.socketCall_lift]
        rfl
      all_goals exact Driver.dumpDispatch_lift hooks rfl _
    rw [native]
    exact product_lift _ (fun h => DispatchFrames.quiet_dispatch facts.lifecycle call h retained up)

theorem observe (facts : H1DriverFrames) :
    ProductPreserves (Driver.observeObserved hooks) := by
  rw [DriverDelivery.observe _ rfl]
  exact PrefixPreserves.bind (idle_timers facts.deferred) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatch_observe (facts : H1DriverFrames) :
    ProductPreserves (Driver.dispatchObserveObserved hooks) := by
  apply PrefixPreserves.bind (observe facts)
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact Outer.lift_modify _ (fun _ => rfl)
  intro _
  exact Outer.socketCallOn _ _ (product_pure ret)

theorem dispatch (facts : H1DriverFrames) (call : Syscall) :
    ProductPreserves (Driver.dispatchObserved hooks call) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _ (retained_dispatch facts)
    (fun attrs => Outer.netlinkRequest _ (product_safe (config_device facts.deferred.worker.quiet facts.configuration attrs)))
    (Outer.rtnetlinkRequest _ (product_native _ (Carrier.create facts.lifecycle)))
    (by
      change ProductPreserves (Driver.dispatchDeleteObserved hooks)
      unfold Driver.dispatchDeleteObserved
      rw [Driver.envDelete_lift hooks rfl rfl rfl]
      exact Outer.rtnetlinkRequest _ (product_lift _ (Environment.delete facts.lifecycle facts.configuration)))
    (syscall_xmit facts.deferred)
    (fun family port message tos ll dest => Outer.socketCallOn _ _ (inject facts.deferred facts.ingress family port message tos ll dest))
    (flood facts.deferred facts.ingress) (batch facts.deferred facts.ingress) (dispatch_observe facts) call

theorem syscall (facts : H1DriverFrames) (call : Syscall) :
    ProductPreserves (Driver.syscallObserved hooks call) :=
  SyscallSource.preserves (fun _ _ hi => hi.2.2.distinct) product_wg_stable call _ _ _ _ _ _ _
    (dispatch facts call) (send_workers facts.deferred) (idle_timers facts.deferred)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit facts.deferred) (after_advance facts.deferred)
    (product_lift _ (Environment.cleanup facts.configuration))

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
