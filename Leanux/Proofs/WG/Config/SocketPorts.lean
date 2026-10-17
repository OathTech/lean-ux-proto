import Leanux.Proofs.WG.Config.Returns
import Leanux.Proofs.WG.Config.Port

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem socketReinit_returns (new4 new6 : Option Nat) (d : Device) :
    Returns (socketReinit new4 new6) (fun g => g.dev = some d)
      (fun _ g => g.dev = some
        { d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort }) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site, outcome, netRx := a.netRxSection}}
  let free (a : Ambient) (sock : Option Nat) : Ambient :=
    let next := mark a .sockFreeNull sock.isNone
    if sock.isNone then next else mark (mark next .iputLastReference true) .iputLazytime false
  let after := free (free (mark ambient .reinitHasNew4 new4.isSome) d.sock4) d.sock6
  let final := {g with dev := some {d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort}}
  refine ⟨(), final, after, ?_, rfl⟩
  cases new4 <;> cases old4 : d.sock4 <;> cases old6 : d.sock6
  all_goals simp [socketReinit, getDev, device, modifyDev, branch, AmbientM.branch,
    sockFree, iputReport, AmbientM.iputReport, old4, old6, final, after, free, mark]
  all_goals rfl

theorem socketInit_nonzero_returns (port : Nat) (nonzero : port ≠ 0)
    (d : Device) (bound : Bool) (net : d.creatingNet = true) :
    Returns (socketInit port) (fun g => g.dev = some d ∧ g.portBound port = bound)
      (fun ret g => if bound || d.sock4 == some port || d.sock6 == some port
        then ret = -EADDRINUSE ∧ g.dev = some d
        else ret = 0 ∧ g.dev = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) := by
  intro g ambient pre
  by_cases held : (bound || d.sock4 == some port || d.sock6 == some port) = true
  · simp only [Bool.or_eq_true, beq_iff_eq] at held
    let mark (a : Ambient) (site : Decision) (outcome : Bool) : Ambient :=
      {a with steps := a.steps.push {decision := site, outcome, netRx := a.netRxSection}}
    let after := mark (mark ambient .iputLastReference true) .iputLazytime false
    refine ⟨-EADDRINUSE, g, after, ?_, ?_⟩
    · simp [socketInit, getDev, pre.1, pre.2, net, nonzero, held,
        iputReport, AmbientM.iputReport, AmbientM.branch, after, mark]
      rfl
    · simp [held, pre.1]
  · simp only [Bool.or_eq_true, beq_iff_eq] at held
    obtain ⟨result, final, after, run, device⟩ :=
      socketReinit_returns (some port) (some port) d g ambient pre.1
    refine ⟨0, final, after, ?_, ?_⟩
    · simp [socketInit, getDev, pre.1, pre.2, net, nonzero, held]
      rw [run]
      rfl
    · simpa [held] using And.intro (rfl : (0 : Int) = 0) device

end Leanux.Proofs.WG.Config
