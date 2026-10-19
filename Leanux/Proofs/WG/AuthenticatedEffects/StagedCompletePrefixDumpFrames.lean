import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProduct

/-! Native dump metadata leaves preserve the literal journal and the
original packet/allocation endpoint. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Dump
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem native (action : WG.M α) (same : SameDump action) :
    Product.StateChecked (liftWGPrefix action) :=
  StateEnsures.quiet (CompleteDump.native action same) (fun _ _ _=>rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Dump
