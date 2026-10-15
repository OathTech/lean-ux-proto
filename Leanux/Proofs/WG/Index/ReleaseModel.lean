import Leanux.Proofs.WG.Index.AllocationModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

def unhashKeypair (d : Device) (id : KeypairId) : Device :=
  { d with indexTable := removeOwner (.keypair id) d.indexTable }

/-- The actual ordered writes, including both unhashes on an immediate final put. -/
def releasedDevice (d : Device) (id : KeypairId) (k : Keypair) (now : Bool) : Device :=
  let unhashed := if now then unhashKeypair d id else d
  let decremented := { unhashed with keypairs := unhashed.keypairs.insert id { k with refcount := k.refcount - 1 } }
  if k.refcount = 1 then
    { unhashKeypair decremented id with keypairs := decremented.keypairs.erase id }
  else decremented

/-- Actual ordered peer writes: decrement first, then unhash and erase on the last put. -/
def releasedPeerDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  let decremented := { d with peers := d.peers.insert pid { p with refcount := p.refcount - 1 } }
  if p.refcount = 1 then
    { decremented with
      indexTable := removeOwner (.handshake pid) decremented.indexTable
      txDropped := decremented.txDropped + p.staged.length, peers := decremented.peers.erase pid }
  else decremented

end Leanux.Proofs.WG.Index
