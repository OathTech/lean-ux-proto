import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionPoll
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionNativeProduct
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionStackFrames

/-! Native stack replies traverse the same observed transmit callback. Inbox
delivery and routing leaves carry direct sent frames; they cannot erase or
manufacture a socket occurrence in the live accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem product_ambient (action : AmbientM α) : ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_native _ (EmissionOuter.ambient action)

macro "emission_stack_failure" : tactic => `(tactic| first
  | (emission_failure_head Stack.excluded; exact PrefixPreserves.lift_failure_bind
      (fun _ _ _ => True.intro) (Env.Stack.excluded _) (stackExcluded_failure _) _)
  | (emission_failure_head invariant; exact PrefixPreserves.lift_failure_bind
      (fun _ _ _ => True.intro) (invariant _) (fun _ => ⟨_,rfl⟩) _)
  | (emission_failure_head unsupported; exact PrefixPreserves.lift_failure_bind
      (fun _ _ _ => True.intro) (unsupported _) (fun _ => ⟨_,rfl⟩) _))

private theorem reply4 (dst : Nat) (bytes : List UInt8) : ProductSafe
    (reply4With (fun family addr packets mtu => liftWGObserver (Driver.transmitObserved hooks family addr packets mtu)) dst bytes) := by
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | emission_stack_failure
    | (emission_poll_head Driver.transmitObserved; exact product_state (device_transmit _ _ _ _))
    | (emission_product_native_head skipCut; exact product_ambient (AmbientM.skipCut _))
    | (emission_product_native_head unsupported; exact product_ambient (AmbientM.unsupported _))
    | (emission_product_native_head liftRouting; exact product_native _ (EmissionOuter.routing _))
    | (emission_product_native_head getDev; exact product_wg _ (state_native _ (by sent_frame [] using [])))
    | emission_product_step

private theorem receive4 (bytes : List UInt8) : ProductSafe
    (receive4With (reply4With (fun family addr packets mtu => liftWGObserver
      (Driver.transmitObserved hooks family addr packets mtu))) bytes) := by
  unfold receive4With
  repeat' first
    | emission_stack_failure
    | (emission_head reply4With; exact reply4 _ _)
    | (emission_product_native_head Stack.excluded; exact product_ambient (AmbientM.unsupported _))
    | (emission_product_native_head invariant; exact product_ambient (AmbientM.invariant _))
    | (emission_product_native_head unsupported; exact product_ambient (AmbientM.unsupported _))
    | (emission_product_native_head liftRouting; exact product_native _ (EmissionOuter.routing _))
    | (emission_product_native_head getWG; exact product_native _ EmissionOuter.read_wg)
    | (emission_product_native_head modifyEnv; exact product_native _ (EmissionOuter.env _))
    | emission_product_step

theorem stack (bytes : List UInt8) : ProductSafe (Driver.stackObserved hooks bytes) := by
  unfold Driver.stackObserved stackReceiveWith
  dsimp only
  split
  · exact receive4 bytes
  · split
    · exact product_native _ (EmissionFrames.stack6 bytes)
    · exact product_ambient (AmbientM.invariant _)

theorem stack_flush (packets : List (List UInt8)) : ProductSafe (Driver.stackFlushObserved hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons packet rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact product_bind (stack packet) (fun _ => ih)

theorem native_poll (pid : PeerId) (budget : Nat) : ProductSafe (Driver.nativePollObserved hooks pid budget) :=
  tagged_poll pid budget stack

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
