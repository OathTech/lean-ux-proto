import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedOuterNative

/-! Namespace cleanup contains no handshake-send callback. Its native socket
and endpoint changes preserve the existing delayed-effect carrier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open Queues
set_option maxHeartbeats 600000

theorem pre_exit : StateSafe (liftWGPrefix netnsPreExit) := by
  apply state_native
  intro h
  unfold netnsPreExit
  simp only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact native_contract _ (socket_native _ (socketReinit_sameSocket _ _)) h)
    | (rx_retention_head clearPeerEndpointSrc; exact native_contract _ (clear_endpoint _) h)
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
    | (rx_retention_head getDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head ForIn.forIn; apply list_view_spec id (Inv h); intro x state; change Preserves (Inv h) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem product_frame_native (action : Leanux.M α) (frame : SameProductStore action) (h : List Event) :
    Preserves (fun w : World => Inv h w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi run
  exact product_store h w v ((ProjectedAction.iff_run _ _ _).mp frame w value v run) hi

theorem env_cleanup (h : List Event) : Preserves (fun w : World => Inv h w.wg) Env.netnsCleanup := by
  have pre : Preserves (fun w : World => Inv h w.wg) (monadLift netnsPreExit : Leanux.M Unit) :=
    native_product_contract _ pre_exit h
  have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => Inv h w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have routes {α : Type} (a : Net.M α) :=
    product_frame_native (monadLift a : Leanux.M α) (fun initial => productRouting_spec a (· = initial)) h
  have env (f : EnvWorld → EnvWorld) : Preserves (fun w : World => Inv h w.wg) (modifyEnv f) := by
    unfold modifyEnv
    exact hoare_modify _ (fun _ hi => hi)
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [pre,effects,routes,env]

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
