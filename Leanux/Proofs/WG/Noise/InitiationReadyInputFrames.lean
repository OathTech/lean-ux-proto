import Leanux.Kernel.Defs

/-! Exact product-state preservation for the initiation input reads. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG

def inputSite (clock : Bool) : HiddenSite := if clock then .tai64nNow else .initEphemeral

theorem hidden_run (clock : Bool) (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = if clock then 16 else 32) (w : World)
    (present : w.ambient.hidden = some ({site := (inputSite clock).info.id, bytes} :: rest)) :
    (hidden (inputSite clock) : Leanux.M (List UInt8)).run w =
      .ok (bytes, {w with ambient := {w.ambient with hidden := some rest}}) := by
  have p1 : HiddenSite.passive 1 = false := by decide
  have p3 : HiddenSite.passive 3 = false := by decide
  have native : (AmbientM.hidden (inputSite clock)).run w.ambient =
      .ok (bytes, {w.ambient with hidden := some rest}) := by
    cases clock <;>
      simp_all [inputSite, AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
        StateT.run, bind, pure, get, getThe, MonadStateOf.get, set, StateT.bind,
        StateT.pure, StateT.get, StateT.set, HiddenSite.info,
        Worker.sectionId, Worker.index, Except.pure, Except.bind,
        List.drop_eq_nil_of_le, List.take_of_length_le]
  change ((AmbientM.hidden (inputSite clock)).run w.ambient >>= fun (value, ambient) =>
    pure (value, {w with ambient})) = _
  rw [native]
  rfl

end Leanux.Proofs.WG.Noise.InitiationReady
