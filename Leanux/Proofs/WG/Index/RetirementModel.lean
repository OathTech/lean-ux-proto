import Leanux.Proofs.WG.Queues.DurableHolders
import Leanux.Proofs.WG.Campaign2.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG
open Queues.RxCredits Queues.RxCredits.DurableHolders

/-- Every dead owner of a hashed keypair has an explicit stamped retirement
reservation. Handshake rows are excluded: a dead peer can still publish one,
and final peer release unhashes its own handshake row. -/
def DeadHashedReserved (retired : Reservations) (d : Device) : Prop :=
  ∀ entry ∈ d.indexTable, ∀ kid key pid p,
    entry.owner = .keypair kid →
    d.keypairs[kid]? = some key →
    key.peer = some pid →
    d.peers[pid]? = some p →
    p.isDead = true →
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ retired

namespace View
/-- Dead hashed-key owners remain covered by the supplied retirement account. -/
def RetirementSafe (retired : Reservations) (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → DeadHashedReserved retired d
end View

end Leanux.Proofs.WG.Index
