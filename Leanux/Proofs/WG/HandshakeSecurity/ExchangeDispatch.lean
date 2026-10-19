import Leanux.Proofs.WG.HandshakeSecurity.DriverDeliveryNeutral
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDispatchFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration TransmitSecurity

theorem retained_dispatch (facts : H1DriverSourceFacts) (traffic : H1TrafficTagFrames)
    (call : Syscall) (retained : DispatchRetained call) :
    ProductPreserves (Driver.retainedObserved ExchangeDriver.hooks call) := by
  by_cases up : call = .wgUp
  · subst call
    exact Outer.socketCallOn _ _ (env_up_checked facts)
  · by_cases down : call = .wgDown
    · subst call
      exact Outer.socketCallOn _ _ (env_down_checked facts)
    · have native : Driver.retainedObserved ExchangeDriver.hooks call = liftPrefix (Leanux.dispatch call) := by
        cases call <;> unfold Driver.retainedObserved
        case wgUp => exact False.elim (up rfl)
        case wgDown => exact False.elim (down rfl)
        all_goals simp only [Driver.dumpDispatch_lift ExchangeDriver.hooks rfl]
      rw [native]
      exact product_lift _ (fun h => DispatchFrames.quiet_dispatch traffic call h retained up down)

theorem observe (facts : H1DriverSourceFacts) :
    ProductPreserves (Driver.observeObserved ExchangeDriver.hooks) := by
  rw [DriverDelivery.observe _ rfl]
  exact PrefixPreserves.bind (idle_timers facts) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatch_observe (facts : H1DriverSourceFacts) :
    ProductPreserves (Driver.dispatchObserveObserved ExchangeDriver.hooks) := by
  apply PrefixPreserves.bind (observe facts)
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact Outer.lift_modify _ (fun _ => rfl)
  intro _
  exact Outer.socketCallOn _ _ (product_pure ret)

theorem dispatch (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames) (call : Syscall) :
    ProductPreserves (Driver.dispatchObserved ExchangeDriver.hooks call) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _ (retained_dispatch facts traffic)
    (fun attrs => Outer.netlinkRequest _ (product_state (config_device facts config attrs)))
    (Outer.rtnetlinkRequest _ (product_native _ (fun h => frame h _ traffic.create)))
    (by
      change ProductPreserves (Driver.dispatchDeleteObserved ExchangeDriver.hooks)
      unfold Driver.dispatchDeleteObserved
      exact Outer.rtnetlinkRequest _ (env_delete_checked facts))
    (syscall_xmit traffic)
    (fun family port message tos ll dest => Outer.socketCallOn _ _ (inject facts traffic family port message tos ll dest))
    (flood facts traffic) (batch facts traffic) (dispatch_observe facts) call

theorem syscall (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames) (traffic : H1TrafficTagFrames) (call : Syscall) :
    ProductPreserves (Driver.syscallObserved ExchangeDriver.hooks call) :=
  SyscallSource.preserves (fun _ _ hi => hi.safe) product_wg_stable call _ _ _ _ _ _ _
    (dispatch facts config traffic call) (send_workers facts) (idle_timers facts)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit facts) (after_advance facts)
    (product_frame _ traffic.cleanup)

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
