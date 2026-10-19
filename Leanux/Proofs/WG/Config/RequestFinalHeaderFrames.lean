import Leanux.Proofs.WG.Config.RequestFinalHeaderModel
import Leanux.Proofs.WG.Config.GetterContextSource

/-! Physical scalar-header projections across metadata, identity and cookie-key writes. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
open Leanux Leanux.WG Noise TimerDiscipline
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

def native (g : WGWorld) := g.dev.map header

theorem metadata {α : Type} {action : WG.M α}
    (frame : SameView getterMetadata action) : SameView native action :=
  frame.of_factor (fun m=>m.map (fun v=>
    (v.1.1,v.1.2.1,v.1.2.2.1,v.1.2.2.2.1,v.1.2.2.2.2.2))) native
    (fun g=>by simp only [getterMetadata,native,Option.map_map,Function.comp_def]; rfl)

theorem identity (key : Key) : SameView native (setStaticIdentityPrivateKey key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd : g.dev with
  | none =>
    simp [setStaticIdentityPrivateKey,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    have source:=setStaticIdentity_run key d g a hd
    rw [run] at source
    cases source
    simp only [native,hd,Option.map_some,header]

theorem cookie : SameView native cookiePrecomputeDeviceKeys := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd : g.dev with
  | none =>
    simp [cookiePrecomputeDeviceKeys,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    have source:=cookiePrecompute_run d g a hd
    rw [run] at source
    cases source
    simp [native,hd,Option.map_some,header,cookieKeysAfter]

end Leanux.Proofs.WG.Config.RequestOrder.FinalHeader
