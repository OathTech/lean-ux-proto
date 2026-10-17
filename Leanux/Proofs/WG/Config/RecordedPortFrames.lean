import Leanux.Proofs.WG.Config.RandomPort

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Socket replacement also preserves the pending hidden-record stream. -/
theorem socketReinit_hidden_returns (new4 new6 : Option Nat) (d : Device)
    (records : Option (List HiddenRecord)) (g : WGWorld) :
    Config.Product.Returns ((socketReinit new4 new6).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = records)
      (fun (_, current) ambient => current.dev = some
        { d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort } ∧ ambient.hidden = records) := by
  intro ambient pre
  let mark (a : Ambient) (site : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site, outcome, netRx := a.netRxSection}}
  let free (a : Ambient) (sock : Option Nat) : Ambient :=
    let next := mark a .sockFreeNull sock.isNone
    if sock.isNone then next else mark (mark next .iputLastReference true) .iputLazytime false
  let after := free (free (mark ambient .reinitHasNew4 new4.isSome) d.sock4) d.sock6
  let final := {g with dev := some {d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort}}
  refine ⟨((), final), after, ?_, rfl, ?_⟩
  · cases new4 <;> cases old4 : d.sock4 <;> cases old6 : d.sock6
    all_goals simp [socketReinit, getDev, pre.1, modifyDev, branch, AmbientM.branch,
      sockFree, iputReport, AmbientM.iputReport, old4, old6, final, after, free, mark]
    all_goals rfl
  · cases old4 : d.sock4 <;> cases old6 : d.sock6
    all_goals simpa [after, free, mark, old4, old6] using pre.2

end Leanux.Proofs.WG.Config
