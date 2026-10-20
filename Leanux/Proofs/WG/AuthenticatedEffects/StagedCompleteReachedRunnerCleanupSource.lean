import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductMetadataFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupMetadataCanonical

/-! The original cleanup callback includes the namespace guard, holder
write, unit resolution, worker section, WG metadata and routing teardown. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

macro "cleanup_product_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact Shape.wg AccountMetadata.preExitShape
  | exact Shape.stored (ProductStore.routeShape _)
  | exact Shape.stored (.reading ProductRead.routingShape)
  | exact Shape.stored (.reading ProductRead.Shape.read)
  | exact Shape.stored (.ambient (get : AmbientM Ambient))
  | exact Shape.stored (.ambient (AmbientM.hidden _))
  | exact Shape.stored (.ambient (AmbientM.skipCut _))
  | exact Shape.stored (.ambient (AmbientM.unsupported _))
  | exact Shape.stored (.ambient _)
  | exact Shape.stored (.write _ (fun _=>rfl))
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def cleanupShape : Shape Env.netnsCleanup := by
  unfold Env.netnsCleanup Env.runWorker
  repeat' cleanup_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductMetadata
