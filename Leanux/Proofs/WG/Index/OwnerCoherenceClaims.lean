import Leanux.Proofs.WG.Index.OwnerCoherenceSource
import Leanux.Proofs.WG.Index.ConsumeFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Original lookup preserves the optional-device owner-coherence invariant
on normal completion, with arbitrary Ambient inputs and no reference upper
bound, readiness or alias-distinctness premise. It does not establish this
invariant for reachable driver states. -/
theorem indexLookup_owner_coherent_safe (kinds : List IndexKind) (index : Nat) :
    Campaign2.Ensures (indexLookup kinds index) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) := by
  intro g ambient result out after pre run final present
  cases device : g.dev with
  | none =>
    have unchanged := indexLookup_cursor kinds index (g.dev.map TimerDiscipline.tableCursor)
      g ambient result out after rfl run
    have absent : out.dev = none := by
      simpa [device] using unchanged
    change out.dev = some final at present
    rw [absent] at present
    cases present
  | some d =>
    have coherent := pre d device
    obtain ⟨actual, output, invariant⟩ :=
      indexLookup_owner_coherence kinds index d coherent g ambient result out after device run
    rw [present] at output
    cases output
    exact invariant

end Leanux.Proofs.WG.Index
