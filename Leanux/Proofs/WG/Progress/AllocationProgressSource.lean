import Leanux.Proofs.WG.Progress.AllocationIterationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Proofs.WG.Noise

/-- The finite evaluator uses the actual native private encounters, selected
once from entry mode. No record format or successful encounter is assumed. -/
def hiddenAllocFinite (site : AllocSite) : AmbientM Bool := do
  let info := site.info
  match info.count with
  | .laxZero => return true
  | .unrecorded => return true
  | .cut => AmbientM.invariant s!"{info.label} is a below-cut consumer, consumed only at a cut point"
  | .exact n =>
    let entry ← get
    let placeholders := entry.hidden.isNone && entry.hiddenPlaceholders
    if !placeholders && !entry.allocArmed.contains info.label then return true
    let encounter := if placeholders then
      (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocPlaceholder) site
      else (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord) site
    let out ← allocationEval n encounter 0
    match out.1 with
    | some result => return result
    | none => return true

theorem hiddenAlloc_finite_source (site : AllocSite) :
    AmbientM.hiddenAlloc site = hiddenAllocFinite site := by
  unfold AmbientM.hiddenAlloc hiddenAllocFinite
  dsimp only
  cases count : site.info.count with
  | laxZero => rfl
  | unrecorded => rfl
  | cut => rfl
  | exact n =>
    apply bind_congr
    intro entry
    by_cases bypass : (!(entry.hidden.isNone && entry.hiddenPlaceholders) &&
        !entry.allocArmed.contains site.info.label) = true
    · simp only [bypass, ite_true]
    · simp only [bypass, Bool.false_eq_true, ite_false]
      let encounter : AmbientM Bool := if entry.hidden.isNone && entry.hiddenPlaceholders then
        (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocPlaceholder) site
        else (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord) site
      have finite : allocationEval n encounter 0 = allocationLoop n encounter (none, 0) :=
        by simpa only [Nat.sub_zero] using (allocationLoop_finite n 0 encounter).symm
      rw [finite]
      apply bind_congr
      intro out
      cases out.1 <;> rfl

/-- The evaluator's encounters are precisely the native helpers. Both bodies
use finite list/byte operations and actual hidden-record consumption; neither
assumes a successful, present, correctly shaped, or steered record. -/
theorem allocation_encounter_sources (site : AllocSite) :
    ((noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord) site =
      (do
        let bytes ← AmbientM.hidden (.alloc site)
        match bytes.headD 2 with
        | 1 => return true
        | 0 => return false
        | b => throw (Stop.hidden s!"{site.info.label}: outcome byte {b}, expected 0 or 1"))) ∧
    ((noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocPlaceholder) site =
      (do
        let entry ← get
        match entry.steerValues.findIdx? (·.1 == site.info.label) with
        | none =>
          if entry.allocSteered.contains site.info.label then
            AmbientM.unsupported s!"steer: an encounter of {site.info.label} beyond its schedule"
          return true
        | some k =>
          set { entry with steerValues := entry.steerValues.eraseIdx k }
          match entry.steerValues[k]!.2 with
          | none => return true
          | some value =>
            if value.length != 8 || value.any (· != 0) then
              throw (Stop.hidden s!"steer: {site.info.label} takes draw or the fail word")
            return false)) := by
  exact ⟨rfl, rfl⟩

end Leanux.Proofs.WG.Progress
