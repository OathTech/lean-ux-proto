import Leanux.Proofs.WG.Index.ReachedIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.Reached
open Lean Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Queues Queues.RxCredits

/-- An empty index has no slot or owner obligations. -/
theorem core_empty (d : Device) (empty : d.indexTable = []) : DeviceIndexCore d := by
  refine ⟨empty_table_safe d empty,hashSlotCoverage_empty d empty,?_,?_⟩
  · intro entry member
    rw [empty] at member
    cases member
  · intro entry member
    rw [empty] at member
    cases member

theorem initial_core (net bare : Bool) : Core (Runner.initialWG net bare) := by
  intro d present
  change (if net && !bare then some { ifindex := 3, ifname := "wg0" } else none) = some d at present
  split at present
  · cases present
    exact core_empty _ rfl
  · cases present

theorem initial_entry (net bare : Bool) (w : World)
    (same : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) :
    Entry [] [] [] w :=
  ⟨HolderEntry.initialized net bare w same,
    core_device (congrArg WGStoreView.dev same) (initial_core net bare)⟩
end Leanux.Proofs.WG.Index.Reached
