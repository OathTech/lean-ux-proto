import Leanux.Proofs.WG.Index.SendFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The session-derived timer changes neither the index table nor its allocation bound. -/
theorem timersSessionDerived_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ timersSessionDerived pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hm := modPeerTimer_tables .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
  have hd := TimerDiscipline.map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ hm
  simpa [timersSessionDerived, Functor.discard, Functor.mapConst, Function.const] using hd

end Leanux.Proofs.WG.Index
