import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.KeyInstall

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem peerGet_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜w.dev = some (withPeer d pid { p with refcount := p.refcount + 1 }) ∧ 0 < p.refcount⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after device run
  by_cases zero : p.refcount = 0
  · simp [peerGet, requireNotPending, refcountInc, branch, branchCmp,
      AmbientM.branch, AmbientM.branchCmp, getPeer, getDev, device, resident,
      zero, unsupported, AmbientM.unsupported] at run
    cases run
  · by_cases overflow : 2147483647 ≤ p.refcount
    · simp [peerGet, requireNotPending, refcountInc, branch, branchCmp,
        AmbientM.branch, AmbientM.branchCmp, getPeer, getDev, device, resident,
        zero, overflow, unsupported, AmbientM.unsupported] at run
      cases run
    · simp [peerGet, requireNotPending, refcountInc, branch, branchCmp,
        AmbientM.branch, AmbientM.branchCmp, getPeer, getDev, device, resident,
        zero, overflow, setPeer, modifyDev] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨rfl, Nat.pos_of_ne_zero zero⟩

end Leanux.Proofs.WG.Config
