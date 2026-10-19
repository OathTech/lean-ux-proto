import Leanux.Proofs.WG.TransmitSecurity.StagedWorkers

/-! Product-state frames for administrative environment actions preserve staged origins. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration

theorem product_routing (action : Net.M α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_store_lift _ (fun initial => productRouting_spec action (fun s => s = initial))

theorem product_env_edit (f : EnvWorld → EnvWorld) : ProductSafe (liftPrefix (modifyEnv f)) := by
  apply product_store_lift
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem idle_device : ProductSafe (liftPrefix Env.requireIdleDevice) :=
  product_store_lift _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store)

theorem inetdev : ProductSafe (liftPrefix Env.inetdevDestroy) :=
  product_store_lift _
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
