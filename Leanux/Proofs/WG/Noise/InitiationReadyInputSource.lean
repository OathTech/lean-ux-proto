import Leanux.Proofs.WG.Noise.InitiationReadyInputFrames
import Leanux.Proofs.WG.Config.Returns

/-! Total native reads of the initiation's exact recorded input bytes. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG

theorem hidden_returns (clock : Bool) (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = if clock then 16 else 32) (d : Device) (g : WGWorld) :
    Config.Product.Returns ((hidden (inputSite clock) : WG.M (List UInt8)).run g)
      (fun ambient => g.dev = some d ∧
        ambient.hidden = some ({site := (inputSite clock).info.id, bytes} :: rest))
      (fun (bs, current) ambient => bs = bytes ∧ current.dev = some d ∧ ambient.hidden = some rest) := by
  intro ambient pre
  have p1 : HiddenSite.passive 1 = false := by decide
  have p3 : HiddenSite.passive 3 = false := by decide
  have native : (AmbientM.hidden (inputSite clock)).run ambient =
      .ok (bytes, {ambient with hidden := some rest}) := by
    cases clock <;>
      simp_all [inputSite, AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
        StateT.run, bind, pure, get, getThe, MonadStateOf.get, set, StateT.bind,
        StateT.pure, StateT.get, StateT.set, HiddenSite.info,
        Worker.sectionId, Worker.index, Except.pure, Except.bind,
        List.drop_eq_nil_of_le, List.take_of_length_le]
  refine ⟨(bytes, g), {ambient with hidden := some rest}, ?_, rfl, pre.1, rfl⟩
  change ((AmbientM.hidden (inputSite clock)).run ambient).map
    (fun (value, after) => ((value, g), after)) = _
  rw [native]
  rfl

end Leanux.Proofs.WG.Noise.InitiationReady
