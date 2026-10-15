import Leanux.Proofs.WG.Progress.DrainOperations
import Leanux.Proofs.WG.TimerDiscipline.SelectionFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Noise TimerDiscipline Std.Do

/-- A normal original resolver result is a member of the supplied queue. The
actual first association and the rejecting membership guard remain in the call. -/
theorem resolveUnit_selected (worker : Worker) (unit : Nat) (queue : List Nat)
    (d : Device) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ resolveUnit worker unit queue
      ⦃⇓? pid w => ⌜w.k.wg = some d ∧ pid ∈ queue⌝⦄ := by
  mvcgen [resolveUnit]
  all_goals simp_all

/-- Selection supplies actual queue membership (or two empty queues), while
ambient peek consumption leaves the captured device unchanged. -/
theorem drainSelect_selected (d : Device) :
    Ensures drainSelect (fun w => w.k.wg = some d)
      (fun selected w => w.k.wg = some d ∧ DrainSelected d selected) := by
  rw [ensures_iff]
  have hs := peekUnit_spec_kernel_variant (fun k => k.wg = some d) .sendWorker
  have hc := peekUnit_spec_kernel_variant (fun k => k.wg = some d) .clearPeerWorker
  have hr := resolveUnit_selected
  mvcgen [drainSelect, getDev, getK, invariant, hs, hc, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [DrainSelected]
  all_goals grind [List.mem_of_head?]

end Leanux.Proofs.WG.Progress
