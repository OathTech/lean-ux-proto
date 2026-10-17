import Leanux.Proofs.WG.Config.RecordedPortFrames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem socketInit_zero_record_tail_returns (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) (g : WGWorld) :
    Config.Product.Returns ((socketInit 0).run g)
      (fun ambient => g.dev = some d ∧
        ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧ g.portBound (drawnPort a b c e) = false)
      (fun (ret, current) ambient => ret = 0 ∧ current.dev = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e } ∧
        ambient.hidden = some rest) := by
  intro ambient pre
  obtain ⟨⟨bytes, middle⟩, next, draw, bytesEq, device, records⟩ :=
    hiddenUdp_record a b c e rest (fun g : WGWorld => g.dev = some d) g ambient ⟨pre.1, pre.2.1⟩
  subst bytes
  obtain ⟨⟨u, final⟩, after, reinit, changed, tail⟩ :=
    socketReinit_hidden_returns (some (drawnPort a b c e)) (some (drawnPort a b c e)) d
      (some rest) middle next ⟨device, records⟩
  refine ⟨(0, final), after, ?_, rfl, changed, tail⟩
  simp only [socketInit, getDev, StateT.run_bind, StateT.run_get, pre.1,
    StateT.run_pure, pure_bind, net, Bool.not_true, Bool.false_eq_true, ite_false,
    beq_self_eq_true, ite_true]
  rw [draw]
  dsimp only [Bind.bind, Except.bind]
  change (((if g.portBound (drawnPort a b c e) || d.sock4 == some (drawnPort a b c e) ||
      d.sock6 == some (drawnPort a b c e) then do
        (unsupported "the random port draw collides with a bound port" : WG.M Unit)
        socketReinit (some (drawnPort a b c e)) (some (drawnPort a b c e))
        pure (0 : Int)
      else do
        socketReinit (some (drawnPort a b c e)) (some (drawnPort a b c e))
        pure (0 : Int)) : WG.M Int).run middle).run next = _
  simp only [pre.2.2, beq_eq_false_iff_ne.mpr free4, beq_eq_false_iff_ne.mpr free6,
    Bool.false_or, Bool.false_eq_true, ite_false]
  simp only [StateT.run_bind, StateT.run_pure]
  rw [reinit]
  rfl

theorem hiddenUdp_run (ambient : Ambient) (a b c d : UInt8) (rest : List HiddenRecord)
    (records : ambient.hidden = some (udpDrawRecord a b c d :: rest)) :
    (AmbientM.hidden .udpPortDraw).run ambient =
      .ok ([a, b, c, d], { ambient with hidden := some rest }) := by
  have passive : HiddenSite.passive 125 = false := by decide
  simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    records, udpDrawRecord, HiddenSite.info, passive, Worker.sectionId, Worker.index, Except.pure, Except.bind]

theorem socketInit_zero_collision (g : WGWorld) (ambient : Ambient) (d : Device) (a b c e : UInt8)
    (rest : List HiddenRecord) (device : g.dev = some d) (net : d.creatingNet = true)
    (records : ambient.hidden = some (udpDrawRecord a b c e :: rest))
    (collision : (g.portBound (drawnPort a b c e) ||
      d.sock4 == some (drawnPort a b c e) || d.sock6 == some (drawnPort a b c e)) = true) :
    ∃ site, ((socketInit 0).run g).run ambient = .error
      (.outsideDomain site "the random port draw collides with a bound port") := by
  have hh := hiddenUdp_run ambient a b c e rest records
  have lifted : ((hidden .udpPortDraw : WG.M (List UInt8)).run g).run ambient =
      .ok (([a, b, c, e], g), {ambient with hidden := some rest}) := by
    change ((AmbientM.hidden .udpPortDraw).run ambient).map
      (fun (value, next) => ((value, g), next)) = _
    rw [hh]
    rfl
  refine ⟨(match ambient.steps.back? with
    | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
    | none => "syscall entry"), ?_⟩
  simp only [socketInit, getDev, StateT.run_bind, StateT.run_get, device,
    StateT.run_pure, pure_bind, net, Bool.not_true, Bool.false_eq_true, ite_false,
    beq_self_eq_true, ite_true]
  rw [lifted]
  dsimp only [Bind.bind, Except.bind]
  change (((if g.portBound (drawnPort a b c e) || d.sock4 == some (drawnPort a b c e) ||
      d.sock6 == some (drawnPort a b c e) then do
        (unsupported "the random port draw collides with a bound port" : WG.M Unit)
        socketReinit (some (drawnPort a b c e)) (some (drawnPort a b c e))
        pure (0 : Int)
      else do
        socketReinit (some (drawnPort a b c e)) (some (drawnPort a b c e))
        pure (0 : Int)) : WG.M Int).run g).run {ambient with hidden := some rest} = _
  simp only [collision, ite_true]
  rfl

end Leanux.Proofs.WG.Config
