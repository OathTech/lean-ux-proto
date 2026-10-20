import Leanux.Proofs.WG.Progress.TimerLoopRecordSource

/-! Physical observation frames used by the recorded deferred tails. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem peekSiteU64_retains (records : List HiddenRecord) (site : HiddenSite) :
    Preserves (fun w : World => Tail records w.ambient.hidden)
      (peekSiteU64 site : Leanux.M (Option UInt64)) := by
  apply liftAmbient_contract (AmbientM.peekSiteU64 site)
    (fun a => Tail records a.hidden) (fun _ a => Tail records a.hidden)
  unfold AmbientM.peekSiteU64
  apply preserves_bind (hoare_consequence (hoare_get _)
    (fun _ h => h) (fun _ _ h => h.2))
  intro a
  exact preserves_pure _

theorem requireDrained_retains (records : List HiddenRecord) (what : String)
    (queues : List Bool) :
    Preserves (fun w : World => Tail records w.ambient.hidden)
      (Env.requireDrained what queues) := by
  have pending : Preserves (fun w : World => Tail records w.ambient.hidden)
      (pendingDeviceUnits : Leanux.M (List Worker)) := by
    apply liftAmbient_contract AmbientM.pendingDeviceUnits
      (fun a => Tail records a.hidden) (fun _ a => Tail records a.hidden)
    unfold AmbientM.pendingDeviceUnits
    apply preserves_bind (hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
    intro a
    exact preserves_pure _
  have fail {α : Type} (message : String) :
      Preserves (fun w : World => Tail records w.ambient.hidden)
        (unsupported message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  have dev : Preserves (fun w : World => Tail records w.ambient.hidden)
      (getDev : Leanux.M Device) := native_product records _ (native_getDev records)
  unfold Env.requireDrained
  repeat' first
    | env_operation_fact pending
    | env_operation_fact dev
    | env_operation_fact fail
    | env_operation_fact product_invariant_retains
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Progress.RecordSuffix
