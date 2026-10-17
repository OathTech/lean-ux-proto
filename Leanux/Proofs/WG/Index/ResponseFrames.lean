import Leanux.Proofs.WG.Index.SendFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The session-derived timer changes neither the index table nor its allocation bound. -/
theorem timersSessionDerived_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ timersSessionDerived pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  have hm := modPeerTimer_tables .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
  have hd := TimerDiscipline.map_result_native_spec (fun _ : Bool => PUnit.unit) _ _ _ hm
  intro g ambient result final after pre run
  obtain ⟨_, _, preserved⟩ := (ensures_iff _ _ _).mpr hd
    g ambient result final after pre run
  exact preserved

end Leanux.Proofs.WG.Index
