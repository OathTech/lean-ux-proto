import Leanux.Proofs.WG.Index.RetirementTransferSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- During the saved mark pass, both old base references and prior retirement
references are reserved. This predicate covers keypair rows, not handshake rows. -/
def AllHashedReserved (reserved : Reservations) (d : Device) : Prop :=
  ∀ entry ∈ d.indexTable, ∀ kid key pid p,
    entry.owner = .keypair kid → d.keypairs[kid]? = some key →
    key.peer = some pid → d.peers[pid]? = some p →
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ reserved

end Leanux.Proofs.WG.Index
