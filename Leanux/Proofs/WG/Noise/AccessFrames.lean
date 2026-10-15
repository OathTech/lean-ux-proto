import Leanux.Proofs.WG.Noise.Execution

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem getPeer_spec (pid : PeerId) (P : World → Prop) :
    ⦃fun w => ⌜P w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P w ∧ peerAt w pid = some p⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals simp_all [peerAt]

theorem setPeer_spec (pid : PeerId) (p : Peer) (P : Peer → Prop) :
    ⦃fun w => ⌜(peerAt w pid).isSome ∧ P p⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜∃ p', peerAt w pid = some p' ∧ P p'⌝⦄ := by
  mvcgen [setPeer, modifyDev, modifyK]
  all_goals dsimp +zetaDelta only at *
  all_goals rename_i w h t
  all_goals cases hw : w.k.wg <;>
    simp_all [peerAt, Std.TreeMap.getElem?_insert]

end Leanux.Proofs.WG.Noise
