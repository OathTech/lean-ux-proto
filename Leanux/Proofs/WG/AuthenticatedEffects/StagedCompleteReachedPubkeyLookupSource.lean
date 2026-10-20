import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLookupFrames

/-! Public-key lookup retains its actual device read and strong peer-reference acquisition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lookup
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def pubkeyShape (key : Key) : Shape (pubkeyLookup key) := by
  simp only [pubkeyLookup,getDev,branch,invariant]
  repeat' lookup_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lookup
