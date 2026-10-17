import Leanux.Proofs.WG.Config.MiddlePageModel
import Leanux.Proofs.WG.Config.PeerPagePlanModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Ordered actual cursor handoffs for nonempty complete-peer pages. Source
correspondence below is only for canonical progressing plans. -/
def peerPagesDevice (current : Device) (old : Option PeerId) : List (List PeerId) → Device
  | [] => current
  | [_] => cursorHandoff current old none
  | page :: next :: rest =>
    peerPagesDevice (cursorHandoff current old page.getLast?) page.getLast? (next :: rest)

/-- Lifetime data only for the last peer of each nonfinal page. These are
ordinary baseline fields, not successful execution or receipt premises. -/
def PeerPageCursorData (peers : PeerId → Peer) : List (List PeerId) → Prop
  | [] => True
  | [_] => True
  | page :: next :: rest =>
    (∀ id, page.getLast? = some id →
      (peers id).isDead = false ∧ 0 < (peers id).refcount ∧ (peers id).refcount+1 < 2^31) ∧
    PeerPageCursorData peers (next :: rest)

/-- Resumed DATA envelope count including a separate final DONE when needed. -/
def peerTailReceiveCount (peers : PeerId → Peer) (pages : List (List PeerId)) : Nat :=
  pages.length + if NLMSG_GOODSIZE-24-multiPeerSpace peers (pages.getLastD []) < nlmsgTotal 4 then 1 else 0

end Leanux.Proofs.WG.Config
