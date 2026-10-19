import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalFactors
import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalModel
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

def observedInitiationTraversal (pid : PeerId) : Leanux.M InitiationTraversalCall := do
  let message ← liftWG (initiationTraversalPrelude pid)
  match message with
  | none => return ⟨none, none⟩
  | some msg =>
    let hook ← dataDoneCapture (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)
    liftWG (initiationTraversalFinish pid msg)
    return ⟨some msg, some hook⟩

theorem observedInitiationTraversal_erase (pid : PeerId) :
    (do let _ ← observedInitiationTraversal pid; pure ()) = liftWG (sendHandshakeInitiation pid) := by
  have unit_drop (action : Leanux.M Unit) : (do action; pure ()) = action := by
    funext entry
    change (action.run entry >>= fun out => Except.ok ((), out.2)) = action.run entry
    cases h : action.run entry with
    | error err => rfl
    | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl
  rw [← initiationTraversal_source pid, liftWG_bind_variant]
  simp only [observedInitiationTraversal, bind_assoc]
  congr 1
  funext message
  cases message with
  | none => rfl
  | some msg =>
    simp only [bind_assoc, pure_bind, unit_drop, initiationTraversalSuffix,
      initiationTraversalSuffixWith, liftWG_bind_variant]
    exact dataDoneCapture_bind _ _ _


end Leanux.Proofs.WG.TimerDiscipline
