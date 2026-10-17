import Leanux.Proofs.WG.Index.OwnerCoherenceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- A last peer reference may be released only after every other hashed owner
has stopped naming it. This is an entry-state obligation, not reachability. -/
def LastOwnerDetached (d : Device) (pid : PeerId) (p : Peer) : Prop :=
  p.refcount = 1 → ∀ e ∈ d.indexTable, e.owner ≠ .handshake pid →
    ownerWord d e.owner ≠ some (some pid)

end Leanux.Proofs.WG.Index
