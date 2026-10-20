import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductMetadataSource

/-! Cleanup's metadata source points retain allocation geometry and the
same packet account, independently of routing, socket and Ambient data. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

def storeView (s : WGStoreView) := AccountMetadata.view
  {dev:=s.dev,peerCounter:=s.peerCounter,keypairCounter:=s.keypairCounter,netIfindexNext:=s.netIfindexNext}

theorem store_view (w : WGWorld) : storeView (wgStoreView w)=AccountMetadata.view w := rfl

theorem Shape.frame (source : Shape action) : SameView (fun w : World=>AccountMetadata.view w.wg) action := by
  induction source with
  | pure value => exact SameView.pure _ _
  | stored source => exact source.frame.factor storeView
  | wg source => exact sameView_liftWG _ AccountMetadata.view _ source.frame (fun _ _ _ same=>same)
  | bind head tail ihHead ihTail => exact SameView.bind ihHead ihTail

theorem Point.projection (point : Point source w v) : AccountMetadata.view v.wg=AccountMetadata.view w.wg := by
  induction point with
  | entry source => rfl
  | returned source performed => exact (ProjectedAction.iff_run _ _ _).mp source.frame _ _ _ performed
  | stored point => exact congrArg storeView point.store
  | wg point => exact point.projection
  | left tail point ih => exact ih
  | right head tail leading point ih => exact ih.trans ((ProjectedAction.iff_run _ _ _).mp head.frame _ _ _ leading)

theorem Point.carrier (point : Point source w v) (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier h v := AccountMetadata.carrier_transport h w v point.projection before

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked (liftPrefix action) := by
  apply PrefixEnsures.lift
  · exact CompleteProduct.carrier_safe
  · intro h w value v before performed
    exact (Point.returned source performed).carrier before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductMetadata
