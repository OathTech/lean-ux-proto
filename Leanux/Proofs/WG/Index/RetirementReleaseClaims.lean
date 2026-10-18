import Leanux.Proofs.WG.Index.RetirementReleaseSource
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Index.FundedBaseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits Queues.RxCredits.DurableHolders

/-- The original peer release preserves hashed-slot coverage with the more
general detachment condition. Queue and timer refusals are retained; only
normal returns have a postcondition. -/
theorem peerPut_hashSlots_detached (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (detached : LastOwnerDetached d pid p) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => s.wg.device = some d ∧ View.HashSlotsSafe s)
      (fun _ s => View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  have device := peerPut_normal_device pid d p resident live g out ambient after result pre.1 run
  intro actual found
  change out.dev = some actual at found
  rw [device] at found
  cases found
  exact releasedPeer_hashSlotCoverage_detached d pid p resident detached (pre.2 d pre.1)

end Leanux.Proofs.WG.Index
