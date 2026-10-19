import Leanux.Proofs.WG.Progress.NativeSuffixSource
import Leanux.Proofs.WG.Progress.JitterProgressSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.TimerDiscipline

theorem skipCutSites_suffix (sites : List HiddenSite) (records : List HiddenRecord) :
    Hoare (AmbientM.skipCutSites sites) (fun a => a.hidden = some records)
      (fun _ a => Tail records a.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after present run
  rcases skipCutSites_outcome sites before records present with
    ⟨taken,rest,final,actual,stored,progress⟩ | ⟨message,actual,_⟩
  · rw [actual] at run
    cases run
    exact ⟨rest,stored,progress.1⟩
  · rw [actual] at run
    cases run

theorem skipCutSites_retains (sites : List HiddenSite) (records : List HiddenRecord) :
    Preserves (fun a => Tail records a.hidden) (AmbientM.skipCutSites sites) :=
  retain_tail Ambient.hidden _ (skipCutSites_suffix sites) records

theorem skipCut_retains (sites : List HiddenSite) (records : List HiddenRecord) :
    Preserves (fun a => Tail records a.hidden) (AmbientM.skipCut sites) := by
  unfold AmbientM.skipCut
  exact preserves_bind (skipCutSites_retains sites records) (fun _ => preserves_pure _)

theorem native_skipCutSites (records : List HiddenRecord) (sites : List HiddenSite) :
    NativeKeeps records (skipCutSites sites) :=
  native_ambient records _ (skipCutSites_retains sites records)

theorem native_skipCut (records : List HiddenRecord) (sites : List HiddenSite) :
    NativeKeeps records (skipCut sites) :=
  native_ambient records _ (skipCut_retains sites records)

theorem jitter_strict (site : JitterSite) (records : List HiddenRecord) (g : WGWorld) :
    Hoare ((jitterBelowRekeyTimeout site.hiddenSite).run g)
      (fun a => a.hidden = some records) (fun _ a => StrictTail records a.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after present run
  rw [jitter_input site records g before present] at run
  have outcome := resolveJitterSearch_outcome site records
  cases actual : resolveJitterSearch site records with
  | error error => rw [actual] at run; cases run
  | ok pair =>
    obtain ⟨jitter,rest⟩ := pair
    rw [actual] at run outcome
    cases run
    exact ⟨rest,rfl,outcome.2⟩

theorem native_jitter (records : List HiddenRecord) (site : JitterSite) :
    NativeKeeps records (jitterBelowRekeyTimeout site.hiddenSite) := by
  intro g
  exact retain_tail Ambient.hidden _ (fun input =>
    hoare_consequence (jitter_strict site input g)
      (fun _ h => h) (fun _ _ h => strict_tail h)) records

theorem native_clockInt (records : List HiddenRecord) (site : HiddenSite) :
    NativeKeeps records (hiddenClock site) := by
  apply native_ambient
  unfold AmbientM.hiddenClock
  exact preserves_bind (hoare_consequence (hidden_after_tail site records)
    (fun _ h => h) (fun _ _ h => strict_tail h)) (fun _ => preserves_pure _)

theorem native_envOk (records : List HiddenRecord) (site : EnvSite) :
    NativeKeeps records (envOk site) := by
  apply native_ambient
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  simp only [AmbientM.envOk,StateT.run_bind,StateT.run_get,StateT.run_set,pure_bind] at run
  cases run
  exact pre

end Leanux.Proofs.WG.Progress.RecordSuffix
