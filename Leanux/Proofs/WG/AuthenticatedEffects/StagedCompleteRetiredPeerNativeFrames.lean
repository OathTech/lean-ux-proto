import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSpineFrames
import Leanux.Proofs.WG.Queues.HolderEncryptFrames
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGSocketLifecycle

/-! Native metadata frames retain one exact holder account. The old holder
witness is preserved through the existing receive/holder projection; upper
accounting is never attached to an unrelated existential funding witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Account.fields (account : Account holders carriers loans w)
    (same : HolderEncrypt.fields v = HolderEncrypt.fields w) : Account holders carriers loans v := by
  have first := congrArg Prod.fst same
  have frame : Frame w v := ⟨congrArg (fun p => p.2.1) same,
    congrArg (fun p => p.2.2.1) same,fun pid batches found => by
      have tx : handoffTxView v = handoffTxView w := congrArg (fun p => p.2.2.2) same
      rw [←tx]; exact found⟩
  exact ⟨⟨account.funded.aligned.frame frame,account.funded.carriers.view (congrArg Prod.fst first)⟩,
    account.upper.peer_view (congrArg (fun s => s.1.1) first),account.stable.view (congrArg Prod.snd first)⟩

theorem ExactBoundary.fields (account : ExactBoundary carriers loans w)
    (same : HolderEncrypt.fields v = HolderEncrypt.fields w) : ExactBoundary carriers loans v := by
  obtain ⟨holders,account⟩ := account
  exact ⟨holders,account.fields same⟩

theorem ExactBoundary.native_fields {action : WG.M α} (same : SameView HolderEncrypt.fields action) :
    Preserves (ExactBoundary carriers loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  exact account.fields ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem ExactBoundary.native_store {action : WG.M α} (same : SameWGStore action) :
    Preserves (ExactBoundary carriers loans) action :=
  ExactBoundary.native_fields (HolderEncrypt.store_fields same)

namespace NativeFrames

theorem configuration {action : WG.M α} (same : SameConfiguration action) :
    SameView HolderEncrypt.fields action := by
  apply same.of_factor (fun s : WGOwnedView => HolderEncrypt.fields
    {dev := s.dev,nlSock7 := s.nlSock7,nlSock8 := s.nlSock8}) HolderEncrypt.fields
  intro w
  cases w with
  | mk dev => cases dev <;> rfl

theorem socket {action : WG.M α} (same : SameSocket action) :
    SameView HolderEncrypt.fields action := by
  apply same.of_factor (fun s : WGOwnedView => HolderEncrypt.fields
    {dev := s.dev,nlSock7 := s.nlSock7,nlSock8 := s.nlSock8}) HolderEncrypt.fields
  intro w
  cases w with
  | mk dev => cases dev <;> rfl

end NativeFrames
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
