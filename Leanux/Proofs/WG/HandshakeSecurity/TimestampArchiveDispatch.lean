import Leanux.Proofs.WG.HandshakeSecurity.DriverDeliveryNeutral
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveDispatchFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration TransmitSecurity

theorem retained_dispatch (call : Syscall)
    (retained : DispatchRetained call) : ProductPreserves (Driver.retainedObserved TimestampDriver.hooks call) := by
  by_cases up : call = .wgUp
  · subst call
    exact Outer.socketCallOn _ _ env_up
  · have native : Driver.retainedObserved TimestampDriver.hooks call = liftPrefix (Leanux.dispatch call) := by
      cases call <;> unfold Driver.retainedObserved
      case wgUp => exact False.elim (up rfl)
      case wgDown =>
        rw [Driver.envDown_lift TimestampDriver.hooks rfl rfl rfl,Driver.socketCall_lift]
        rfl
      all_goals exact Driver.dumpDispatch_lift TimestampDriver.hooks rfl _
    rw [native]
    exact product_lift _ (fun h => Frames.quiet_dispatch call h retained up)

theorem observe :
    ProductPreserves (Driver.observeObserved TimestampDriver.hooks) := by
  rw [DriverDelivery.observe _ rfl]
  exact PrefixPreserves.bind (idle_timers) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatch_observe :
    ProductPreserves (Driver.dispatchObserveObserved TimestampDriver.hooks) := by
  apply PrefixPreserves.bind (observe)
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact Outer.lift_modify _ (fun _ => rfl)
  intro _
  exact Outer.socketCallOn _ _ (product_pure ret)

theorem dispatch (call : Syscall) :
    ProductPreserves (Driver.dispatchObserved TimestampDriver.hooks call) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _ (retained_dispatch)
    (fun attrs => Outer.netlinkRequest _ (product_safe (config_device attrs)))
    (Outer.rtnetlinkRequest _ (product_native _ device_create))
    (by
      change ProductPreserves (Driver.dispatchDeleteObserved TimestampDriver.hooks)
      unfold Driver.dispatchDeleteObserved
      rw [Driver.envDelete_lift TimestampDriver.hooks rfl rfl rfl]
      exact Outer.rtnetlinkRequest _ (product_lift _ (env_delete)))
    syscall_xmit
    (fun family port message tos ll dest => Outer.socketCallOn _ _ (inject family port message tos ll dest))
    (flood) (batch) (dispatch_observe) call

theorem syscall (call : Syscall) :
    ProductPreserves (Driver.syscallObserved TimestampDriver.hooks call) :=
  SyscallSource.preserves (fun _ _ hi => hi.1) product_wg_stable call _ _ _ _ _ _ _
    (dispatch call) (send_workers) (idle_timers)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit) (after_advance)
    (product_lift _ env_cleanup)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
