import Leanux.Proofs.WG.Progress.NativeSuffixSource
import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.Framing.Stack
import Leanux.Proofs.WG.Lifetimes.AllocationReleaseFrames
/-! The complete original IPv6 stack-delivery action retains a supplied-record suffix on normal return. This does not cover the separate IPv4 route/reply path. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing
theorem stackReceive6_retains (records : List HiddenRecord) (pkt : List UInt8) :
    Preserves (fun w:World=>Tail records w.ambient.hidden) (Env.Stack.receive6 pkt) := by
  let P := fun w:World=>Tail records w.ambient.hidden
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
    exact pre
  have write (f : EnvWorld→EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
    exact pre
  have bad (message : String) : Preserves P (invariant message : Leanux.M Unit) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  have excluded (row : String) : Preserves P (Env.Stack.excluded row) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    obtain ⟨e,fail⟩ := stackExcluded_failure row before
    rw [fail] at run
    cases run
  change Preserves P _
  unfold Env.Stack.receive6
  repeat' first
    | env_operation_fact read
    | env_operation_fact write
    | env_operation_fact bad
    | env_operation_fact excluded
    | (allocation_release_head Bind.bind; apply preserves_bind)
    | (allocation_release_head Pure.pure; exact preserves_pure _)
    | env_operation_step
end Leanux.Proofs.WG.Progress.RecordSuffix
