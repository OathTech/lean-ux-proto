import Leanux.Proofs.WG.Index.LifecycleSource
import Leanux.Proofs.WG.Index.NewlinkFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem wgNewlink_tables : Ensures wgNewlink
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hc := cookieCheckerInit_tables
  have hp := pubkeyHashtableAlloc_tables
  have hr := ratelimiterInit_tables
  have hs := TimerDiscipline.skipCut_spec_kernel_variant TablesSafeKernel
  have he := skipCutExactly_spec_kernel_variant TablesSafeKernel
  rw [ensures_iff]
  mvcgen [wgNewlink, envOk, mayHaveSlept, branch, getK, modifyDev, modifyK,
    unsupported, hc, hp, hr, hs, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem wgSetup_tables_spec :
    ⦃fun _ => ⌜True⌝⦄ wgSetup ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  obtain ⟨r, v, execution, device⟩ := wgSetup_device w pre
  rw [run] at execution
  cases execution
  intro d present
  rw [device] at present
  cases present
  exact setupDevice_safe

/-- Existing devices return EEXIST; otherwise setup initializes the table,
newlink preserves it, and a normally returning negative result removes it. -/
theorem wgCreate_tables : Ensures wgCreate
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hs := wgSetup_tables_spec
  have hn := (ensures_iff _ _ _).mp wgNewlink_tables
  rw [ensures_iff]
  mvcgen [wgCreate, getK, modifyK, hs, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel]

/-- The unchanged deletion prefix after the initial device-presence test.
The down operation and record consumers may stop. -/
def deletePrefix : M Unit := do
  if (← getDev).running then wgDown
  skipCut allocCuts
  mayHaveSlept

theorem wgDelete_source : wgDelete = (do
    if (← getK).wg.isNone then return -ENODEV
    deletePrefix
    wgDestruct
    return 0) := by
  simp only [wgDelete, deletePrefix, bind_assoc]
  congr 1
  funext k
  split
  · rfl
  · congr 1
    funext d
    split <;> simp only [bind_assoc, pure_bind]

/-- Normal deletion leaves no device, including the already-absent ENODEV arm.
The original destructor supplies absence on the existing-device arm. -/
theorem wgDelete_absent : Ensures wgDelete (fun _ => True)
    (fun _ w => w.k.wg = none) := by
  have hp : ⦃fun _ => ⌜True⌝⦄ deletePrefix ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w result final pre run
    trivial
  have hd := (ensures_iff _ _ _).mp wgDestruct_absent
  rw [wgDelete_source, ensures_iff]
  mvcgen [getK, hp, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.Index
