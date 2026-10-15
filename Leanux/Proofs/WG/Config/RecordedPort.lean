import Leanux.Proofs.WG.Config.RandomPort

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem socketReinit_hidden_returns (new4 new6 : Option Nat) (d : Device)
    (records : Option (List HiddenRecord)) :
    Returns (socketReinit new4 new6) (fun w => w.k.wg = some d ∧ w.hidden = records)
      (fun _ w => w.k.wg = some
        { d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort } ∧ w.hidden = records) := by
  rw [returns_iff]
  cases new4 <;> simp only [socketReinit, Option.isSome_some, Option.isSome_none,
    Option.getD_none, Option.getD_some]
  all_goals mvcgen [sockFree, iputReport, branch, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

theorem socketInit_zero_record_tail_returns (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Returns (socketInit 0)
      (fun w => w.k.wg = some d ∧
        w.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e } ∧
        w.hidden = some rest) := by
  have hh := hiddenUdp_record a b c e rest (fun k => k.wg = some d)
  have hs := fun port => (returns_iff _ _ _).mp
    (socketReinit_hidden_returns (some port) (some port) d (some rest))
  rw [returns_iff]
  simp [socketInit]
  mvcgen [getDev, getK, invariant, unsupported, hh, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [drawnPort]
  all_goals grind only

theorem hiddenUdp_run (w : World) (a b c d : UInt8) (rest : List HiddenRecord)
    (records : w.hidden = some (udpDrawRecord a b c d :: rest)) :
    (hidden .udpPortDraw).run w = .ok ([a, b, c, d], { w with hidden := some rest }) := by
  have passive : HiddenSite.passive 125 = false := by decide
  simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, modify, modifyGet, StateT.bind, StateT.pure, StateT.get, StateT.set,
    records, udpDrawRecord, HiddenSite.info, passive, Worker.sectionId, Worker.index, Except.pure, Except.bind]

theorem socketInit_zero_collision (w : World) (d : Device) (a b c e : UInt8)
    (rest : List HiddenRecord) (device : w.k.wg = some d) (net : d.creatingNet = true)
    (records : w.hidden = some (udpDrawRecord a b c e :: rest))
    (collision : (w.portBound (drawnPort a b c e) ||
      d.sock4 == some (drawnPort a b c e) || d.sock6 == some (drawnPort a b c e)) = true) :
    ∃ site, (socketInit 0).run w = .error
      (.outsideDomain site "the random port draw collides with a bound port") := by
  have hh := hiddenUdp_run w a b c e rest records
  change hidden .udpPortDraw w = .ok ([a, b, c, e], { w with hidden := some rest }) at hh
  refine ⟨(match w.steps.back? with
    | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
    | none => "syscall entry"), ?_⟩
  simp [socketInit, getDev, getK, unsupported, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, modify, modifyGet, StateT.bind,
    StateT.pure, StateT.get, StateT.set, Except.pure, Except.bind,
    device, net, hh, drawnPort] at *
  simp only [ite_eq_left collision]
  rfl

end Leanux.Proofs.WG.Config
