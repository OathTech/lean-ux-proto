import Leanux.Proofs.WG.HandshakeSecurity.DriverDeliveryNeutral
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceCleanup
import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceDispatchFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration TransmitSecurity

theorem retained_dispatch (call : Syscall) (retained : DispatchRetained call) :
    ProductPreserves (E := E) (Driver.retainedObserved EntrySource.hooks (E := E) call) := by
  by_cases up : call = .wgUp
  · subst call
    exact Outer.socketCallOn _ _ (env_up_observed)
  · by_cases down : call = .wgDown
    · subst call
      exact Outer.socketCallOn _ _ (env_down_observed)
    · have native : Driver.retainedObserved EntrySource.hooks (E := E) call = liftPrefix (Leanux.dispatch call) := by
        cases call <;> unfold Driver.retainedObserved
        case wgUp => exact False.elim (up rfl)
        case wgDown => exact False.elim (down rfl)
        all_goals rfl
      rw [native]
      exact Outer.lift_spec _ (fun h => DispatchFrames.quiet_dispatch call h retained up down)

theorem observe :
    ProductPreserves (E := E) (Driver.observeObserved EntrySource.hooks (E := E)) := by
  rw [DriverDelivery.observe _ rfl]
  exact PrefixPreserves.bind (idle_timers) (fun _ => product_store _ observeTail_sameKernel)

theorem dispatch_observe :
    ProductPreserves (E := E) (Driver.dispatchObserveObserved EntrySource.hooks (E := E)) := by
  apply PrefixPreserves.bind (observe)
  rintro ⟨ret,observed⟩
  dsimp only
  apply PrefixPreserves.bind
  · exact Outer.lift_modify _ (fun _ => rfl)
  intro _
  exact Outer.socketCallOn _ _ (product_pure ret)

theorem dispatch (call : Syscall) :
    ProductPreserves (E := E) (Driver.dispatchObserved EntrySource.hooks (E := E) call) :=
  dispatchWith_preserves _ _ _ _ _ _ _ _ _ (retained_dispatch)
    (fun attrs => Outer.netlinkRequest _ (product_safe (config_device attrs)))
    (Outer.rtnetlinkRequest _ (product_native _ device_create))
    (by
      change ProductPreserves (E := E) (Driver.dispatchDeleteObserved EntrySource.hooks (E := E))
      unfold Driver.dispatchDeleteObserved
      exact Outer.rtnetlinkRequest _ (env_delete_observed))
    (syscall_xmit)
    (fun family port message tos ll dest => Outer.socketCallOn _ _ (inject family port message tos ll dest))
    (flood) (batch) (dispatch_observe) call

theorem syscall (call : Syscall) :
    ProductPreserves (E := E) (Driver.syscallObserved EntrySource.hooks (E := E) call) :=
  SyscallSource.preserves (fun _ _ hi => hi.1) product_wg_stable call _ _ _ _ _ _ _
    (dispatch call) (send_workers) (idle_timers)
    (product_store _ routeIntoWg0_sameKernel) (after_xmit) (after_advance)
    (product_lift _ env_cleanup)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
