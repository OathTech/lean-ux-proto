import Leanux.Proofs.WG.Config.Returns

/-! Full-product read preservation through the runner's actual WireGuard lift. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem sessionReadyPeer_read (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (P : World → Prop) :
    Config.Product.Returns (liftWG (getPeer pid)) (fun w => w.wg.dev = some d ∧ P w)
      (fun result w => result = p ∧ w.wg.dev = some d ∧ P w) := by
  intro w pre
  refine ⟨p, w, ?_, rfl, pre⟩
  change (do
    let ((result, g), a) ← ((getPeer pid).run w.wg).run w.ambient
    pure (result, {w with wg := g, ambient := a})) = Except.ok (p, w)
  simp [getPeer, getDev, pre.1, resident]
  rfl

end Leanux.Proofs.WG.Noise
