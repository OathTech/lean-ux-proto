import Leanux.Proofs.WG.Index.RetirementModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.WG.State

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG
open Queues.RxCredits

/-- Dequeueing one clear-work occurrence changes no field used by the
retirement predicate. This is a frame for the original device write. -/
theorem clearQueueErase_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures
      (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
      (View.RetirementSafe retired) (fun _ => View.RetirementSafe retired) := by
  intro w a value v b hi actual
  cases actual
  intro d found
  change (w.dev.map fun old => {old with clearWorkQueue := old.clearWorkQueue.erase pid}) =
    some d at found
  cases device : w.dev with
  | none => simp [device] at found
  | some old =>
    simp only [device,Option.map_some,Option.some.injEq] at found
    subst d
    exact hi old device

end Leanux.Proofs.WG.Index
