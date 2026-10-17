import Leanux.Proofs.WG.Config.MixedPageDeviceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Unconsing a nonterminal plan exposes only the current computed cursor's
data and retains the same condition on the rest. -/
theorem mixedPlanCursorData_cons (base : Device) (page next : MixedPeerScan)
    (rest : List MixedPeerScan) :
    MixedPlanCursorData base (page::next::rest) ↔
      (∀ id, page.native.2.1 = some id →
        ∃ p, base.peers[id]? = some p ∧ p.isDead = false ∧ 0 < p.refcount ∧
          p.refcount+1+(if page.native.1.nextPeer = some id then 1 else 0) < 2^31) ∧
      MixedPlanCursorData base (next::rest) := by
  simp only [MixedPlanCursorData,List.dropLast_cons_cons,List.mem_cons,forall_eq_or_imp]

end Leanux.Proofs.WG.Config
