import Leanux.Proofs.WG.Index.FundedBaseSource
import Leanux.Proofs.WG.Index.InitializedBoundsClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedFunding
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

/-- Every nondead resident has its actual base-list occurrence and a positive
reference. This makes no claim about already-retired peers or hashed keys. -/
def LivePeerCredit (s : Campaign2.Snapshot) : Prop :=
  ∀ d pid p, s.wg.device = some d → d.peers[pid]? = some p →
    p.isDead = false → pid ∈ d.peerList ∧ 0 < p.refcount

end Leanux.Proofs.WG.Index.InitializedFunding
