import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSavedPeerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedFrames

/-! The actual read, rather than an incoming packet-account premise at a cut,
supplies the peer fields used by a delayed metadata write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Shape.preserves {α : Type} {body : WG.M α} (source : Shape pid saved body) (P : _ → Prop) :
    Preserves (fun w=>P (StagedEntry.view w) ∧ SavedFrames.PeerFields pid saved w) body := by
  induction source with
  | pure value=>exact hoare_consequence (hoare_pure value _) (fun _ before=>before) (fun _ _ after=>after.2)
  | read=>exact hoare_consequence (hoare_get _) (fun _ before=>before) (fun _ _ after=>after.2)
  | ambient body=>exact hoare_liftAmbient _ _
  | write value same=>exact SavedFrames.write_saved pid saved value P same
  | bind head tail ihHead ihTail=>exact preserves_bind ihHead ihTail

theorem Point.frame {α : Type} {body : WG.M α} {source : Shape pid saved body}
    (point : Point source w a v b)
    (savedFields : SavedFrames.PeerFields pid saved w) :
    StagedEntry.view v=StagedEntry.view w ∧ SavedFrames.PeerFields pid saved v := by
  revert savedFields
  induction point with
  | entry source=>intro fields; exact ⟨rfl,fields⟩
  | returned source performed=>
      intro fields
      exact (hoare_iff_run_ambient _ _ _).mp (source.preserves (·=StagedEntry.view _)) _ _ _ _ _ ⟨rfl,fields⟩ performed
  | left tail point ih=>exact ih
  | right head tail leading point ih=>
      intro fields
      have prior:=(hoare_iff_run_ambient _ _ _).mp (head.preserves (·=StagedEntry.view _)) _ _ _ _ _ ⟨rfl,fields⟩ leading
      obtain ⟨same,fields⟩:=ih prior.2
      exact ⟨same.trans prior.1,fields⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedPeer
