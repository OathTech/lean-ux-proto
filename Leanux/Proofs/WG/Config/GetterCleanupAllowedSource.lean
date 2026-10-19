import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Config.GetterCleanupMacFrames
import Leanux.Proofs.WG.Config.ReplacementCompletionSource
import Leanux.Proofs.WG.Index.CreatorSource
import Leanux.Proofs.WG.Index.SenderIndexSource
import Leanux.Proofs.WG.Index.BulkRemovalSource
import Leanux.Proofs.WG.Roaming.RemoteTimerFrames
import Leanux.Proofs.WG.Config.AllowedRemovalReadbackFrames
import Leanux.Proofs.WG.Index.AllowedFrameSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterCleanup
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do

/-- Generic preservation over C1's exact root-removal source factor. The
node actions remain typed Aip calls; the list deletion is the actual native call. -/
theorem rootRemove_preserves_source (P : WGWorld → Prop)
    (node : ∀id,Preserves P (liftAip (getNode id)))
    (delete : ∀id,Preserves P (listDel id)) (root : NodeId) :
    Preserves P (rootRemovePeerLists root) := by
  have read : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a x v b pre run
    cases hd : g.dev with
    | none => simp [getDev,hd,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev,hd] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact pre
  have peer (pid : PeerId) : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_spec pid P) (fun _ h=>h) (fun _ _ h=>h.1)
  have push (xs : List (Option NodeId)) (stack : List NodeId) :
      Preserves P (AllowedIps.pushChildren xs stack) := by
    unfold AllowedIps.pushChildren
    apply Framing.list_view_spec id P
    intro c s
    change Preserves P _
    unfold AllowedIps.pushChild
    repeat' first
      | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) P)
      | rx_retention_step
  have step (i : Nat) (state : Option Unit × List NodeId) :
      Preserves P (AllowedIps.rootRemoveStep i state) := by
    unfold AllowedIps.rootRemoveStep
    repeat' first
      | (allocation_release_lift_from AipM; exact node _)
      | (rx_retention_head AllowedIps.pushChildren; exact push _ _)
      | (rx_retention_head getPeer; exact peer _)
      | (rx_retention_head listDel; exact delete _)
      | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) P)
      | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) P)
      | rx_retention_step
  rw [←AllowedIps.rootRemoveSource_eq]
  unfold AllowedIps.rootRemoveSource
  apply preserves_bind read
  intro d
  apply preserves_bind
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    exact Framing.list_view_spec id P _ _ _ step
  · intro out
    cases out.1
    · exact hoare_liftAmbient (AmbientM.invariant _) P
    · exact preserves_pure _

end Leanux.Proofs.WG.Config.GetterCleanup
