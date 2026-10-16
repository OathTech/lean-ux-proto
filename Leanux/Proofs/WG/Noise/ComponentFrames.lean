import Leanux.Proofs.WG.Noise.Execution

/-! Local variants of the campaign-1 component adapters. These expose the
native StateT/Std.Do contracts without importing the lagging shared layer.
Ambient actions preserve the outer state; index actions retain the device
guard and write back only the index table. -/
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem hoare_liftAmbient_variant (a : AmbientM α) (P : σ → Prop) :
    ⦃fun s => ⌜P s⌝⦄ (StateT.lift a : StateT σ AmbientM α)
      ⦃⇓? _ s => ⌜P s⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro s ambient x s' ambient' hp hr
  change (a.run ambient >>= fun (value, next) => Except.ok ((value, s), next)) =
    .ok ((x, s'), ambient') at hr
  cases ha : a.run ambient with
  | error e => rw [ha] at hr; cases hr
  | ok out =>
    rcases out with ⟨value, next⟩
    rw [ha] at hr
    cases hr
    exact hp

theorem liftIndex_run_variant (a : WG.IndexM α) (g : WGWorld) (ambient : Ambient) :
    ((WG.liftIndex a).run g).run ambient =
      match g.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => ((a.run d.indexTable).run ambient).map
          (fun ((x, table), ambient') =>
            ((x, {g with dev := some {d with indexTable := table}}), ambient')) := by
  cases hd : g.dev with
  | none =>
    simp [WG.liftIndex, WG.getDev, hd, invariant, AmbientM.invariant]
    rfl
  | some d =>
    simp only [WG.liftIndex, WG.getDev, StateT.run_bind, StateT.run_pure]
    cases ha : (a.run d.indexTable).run ambient <;>
      simp [WG.modifyDev, hd, ha] <;> rfl

theorem hoare_liftIndex_variant (a : WG.IndexM α) (P : WGWorld → Prop)
    (stable : ∀ g d table, P g → g.dev = some d →
      P {g with dev := some {d with indexTable := table}}) :
    ⦃fun g => ⌜P g⌝⦄ WG.liftIndex a ⦃⇓? _ g => ⌜P g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient x g' ambient' hp hr
  rw [liftIndex_run_variant] at hr
  cases hd : g.dev with
  | none => simp [hd] at hr
  | some d =>
    simp only [hd] at hr
    cases ha : (a.run d.indexTable).run ambient with
    | error e => simp [ha, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨y, table⟩, b⟩
      simp [ha, Except.map] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact stable g d table hp hd

end Leanux.Proofs.WG.Noise
