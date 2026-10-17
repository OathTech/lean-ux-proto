import Leanux.Proofs.WG.Config.QuietModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Empty work queues preserve the full original product, including Ambient and fixture. -/
theorem drain_empty (upTo : Option PeerId) (d : Device) (w : World)
    (resident : w.wg.dev = some d) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    (liftWG (drainHandshakeSendWq upTo)).run w = .ok ((), w) := by
  have run : ((drainHandshakeSendWq upTo).run w.wg).run w.ambient =
      .ok (((), w.wg), w.ambient) := by
    unfold drainHandshakeSendWq
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size]
    rw [List.range'_succ, List.forIn_cons]
    simp [getDev, resident, send, clear, StateT.run, StateT.bind, StateT.pure,
      bind, pure, get, getThe, MonadStateOf.get, StateT.get, Except.bind, Except.pure]
  change (((drainHandshakeSendWq upTo).run w.wg).run w.ambient >>= fun ((value, state), ambient) =>
    .ok (value, {w with wg := state, ambient := ambient})) = _
  rw [run]
  rfl

end Leanux.Proofs.WG.Config
