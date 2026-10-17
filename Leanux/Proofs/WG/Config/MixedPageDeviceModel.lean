import Leanux.Proofs.WG.Config.MixedPageScanModel
import Leanux.Proofs.WG.Config.MiddlePageModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Original ordered Device effects of the planned cursor handoffs. -/
def mixedPagesDevice (current : Device) : List MixedPeerScan → Device
  | [] => current
  | page::pages => mixedPagesDevice
      (cursorHandoff current page.native.1.nextPeer
        (if page.native.2.2.2.1 then none else page.native.2.1)) pages

/-- Only computed nonfinal cursors require lifetime data. Reacquisition of
the held cursor needs its second increment; other peer counts are unrestricted. -/
def MixedPlanCursorData (base : Device) (pages : List MixedPeerScan) : Prop :=
  ∀ page ∈ pages.dropLast, ∀ id, page.native.2.1 = some id →
    ∃ p, base.peers[id]? = some p ∧ p.isDead = false ∧ 0 < p.refcount ∧
      p.refcount+1+(if page.native.1.nextPeer = some id then 1 else 0) < 2^31

end Leanux.Proofs.WG.Config
