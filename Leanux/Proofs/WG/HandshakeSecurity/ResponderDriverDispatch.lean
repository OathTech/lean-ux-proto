import Leanux.Proofs.WG.HandshakeSecurity.DriverDeliveryNeutral
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDispatchFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration TransmitSecurity

theorem retained_dispatch (H1 : H1ResponderCurrentEdges) (call : Syscall)
    (retained : DispatchRetained call) : ProductPreserves (Driver.retainedObserved hooks call) := by
  by_cases up : call = .wgUp
  · subst call
    exact Outer.socketCallOn _ _ env_up
  · have native : Driver.retainedObserved hooks call = liftPrefix (Leanux.dispatch call) := by
      cases call <;> unfold Driver.retainedObserved
      case wgUp => exact False.elim (up rfl)
      case wgDown =>
        rw [Driver.envDown_lift hooks rfl rfl,Driver.socketCall_lift]
        rfl
      all_goals rfl
    rw [native]
    exact product_lift _ (fun h => Frames.quiet_dispatch H1 call h retained up)

theorem observe (H1 : H1ResponderCurrentEdges) :
    ProductPreserves (Driver.observeObserved hooks) := by
  rw [DriverDelivery.observe _ rfl]
  exact PrefixPreserves.bind (idle_timers H1) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatch_observe (H1 : H1ResponderCurrentEdges) :
    ProductPreserves (Driver.dispatchObserveObserved hooks) := by
  apply PrefixPreserves.bind (observe H1)
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact Outer.lift_modify _ (fun _ => rfl)
  intro _
  exact Outer.socketCallOn _ _ (product_pure ret)

theorem dispatch (H1 : H1ResponderCurrentEdges) (call : Syscall) :
    ProductPreserves (Driver.dispatchObserved hooks call) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _ (retained_dispatch H1)
    (fun attrs => Outer.netlinkRequest _ (product_safe (config_device H1 attrs)))
    (Outer.rtnetlinkRequest _ (product_native _ carrier_device_create))
    (by
      change ProductPreserves (Driver.dispatchDeleteObserved hooks)
      unfold Driver.dispatchDeleteObserved
      rw [Driver.envDelete_lift hooks rfl rfl rfl]
      exact Outer.rtnetlinkRequest _ (product_lift _ (carrier_env_delete H1)))
    syscall_xmit
    (fun family port message tos ll dest => Outer.socketCallOn _ _ (inject H1 family port message tos ll dest))
    (flood H1) (batch H1) (dispatch_observe H1) call

theorem syscall (H1 : H1ResponderCurrentEdges) (call : Syscall) :
    ProductPreserves (Driver.syscallObserved hooks call) :=
  SyscallSource.preserves (fun _ _ hi => hi.2) product_wg_stable call _ _ _ _ _ _ _
    (dispatch H1 call) (send_workers H1) (idle_timers H1)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit H1) (after_advance H1)
    (product_lift _ carrier_env_cleanup)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
