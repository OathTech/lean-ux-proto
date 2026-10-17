import Leanux.Proofs.WG.Index.OwnerCoherenceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

def ownerReferences (d : Device) :=
  (d.indexTable, d.keypairs, fun pid : PeerId =>
    d.peers[pid]?.map (fun p => (p.handshakeEntryPeer, p.refcount)))

def referencesAt (d : Device) (g : WGWorld) : Prop :=
  g.dev.map ownerReferences = some (ownerReferences d)

end Leanux.Proofs.WG.Index
