import Leanux.Proofs.WG.Config.ScalarFinishEffects
import Leanux.Proofs.WG.Config.PeerScalarRetentionFrames

/-! Projection of the existing single staging/release source contracts; deletion remains permitted by these backward frames. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarFinish
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention

theorem staged_selected (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>Selected pid expected (view g)) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  exact selected_retained (frame_retained
    (Index.StagingRich.sendStagedPackets_rich pid g g a result final b
      (Index.StagingRich.refl g) run)) pre

theorem keepalive_selected (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>Selected pid expected (view g)) (sendKeepalive pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  exact selected_retained (frame_retained
    (Index.StagingRich.sendKeepalive_rich pid g g a result final b
      (Index.StagingRich.refl g) run)) pre

theorem put_selected (peer : Option PeerId) (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>Selected pid expected (view g)) (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  exact selected_retained (frame_retained
    (Index.StagingRich.peerPut_rich g peer g a result final b
      (Index.StagingRich.refl g) run)) pre

theorem read_selected (pid : PeerId) (expected : Cell) :
    Preserves (fun g=>Selected pid expected (view g)) getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  cases hd : g.dev with
  | none => simp [getDev,hd,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    simp [getDev,hd] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre

end Leanux.Proofs.WG.Config.ScalarFinish
