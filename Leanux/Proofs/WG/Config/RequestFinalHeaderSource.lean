import Leanux.Proofs.WG.Config.KeyStagePreservationSource
import Leanux.Proofs.WG.Config.RequestFinalHeaderFrames
import Leanux.Proofs.WG.Config.RequestOrderInspectionSource

/-! The existing key-stage factor and generic keyFinish contracts preserve scalar fields. The normal inspection bridge applies a contract to the same original execution; it creates no new observer. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
open Leanux Leanux.WG Noise TimerDiscipline
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem contracts (initial : Option Header) :
    Index.ConfigurationKeyRules.Contracts (fun g=>native g=initial) where
  read := (metadata GetterCleanup.read_device).wp (fun v=>v=initial)
  identity key := (identity key).wp (fun v=>v=initial)
  cookie := cookie.wp (fun v=>v=initial)
  precompute pid := (metadata (GetterPeerCommand.precompute pid)).wp (fun v=>v=initial)
  expire pid := (metadata (GetterContext.expire pid)).wp (fun v=>v=initial)
  staged pid := (metadata (GetterStaging.staged pid)).wp (fun v=>v=initial)
  conflict key := (metadata (GetterContext.conflict key)).wp (fun v=>v=initial)

theorem collision (key : Key) : SameView native (keyCollisionSource key) := by
  intro initial
  exact KeyStage.collision_preserves _ (contracts initial) key

theorem stage (attrs : DeviceAttrs) : SameView native (keyStage attrs) := by
  intro initial
  exact KeyStage.stage_preserves _ (contracts initial) attrs


theorem matches_normal_ensures (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (matched : Matches attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (P : Campaign2.Snapshot→Prop) (Q : Int→Campaign2.Snapshot→Prop)
    (contract : Campaign2.Ensures (wgSetDevice attrs) P Q) (pre : P initial) :
    Q ret final := by
  obtain ⟨g,a,rfl,rfl⟩:=matched
  have original:=(inspection_outcome attrs g a).symm.trans normal
  cases run : ((wgSetDevice attrs).run g).run a with
  | error stop =>
    simp only [Campaign2.observeResult,run,Except.map] at original
    cases original
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩:=out
    simp only [Campaign2.observeResult,run,Except.map,Except.ok.injEq,Prod.mk.injEq] at original
    obtain ⟨rfl,rfl⟩:=original
    exact contract g a value v b pre run

end Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
