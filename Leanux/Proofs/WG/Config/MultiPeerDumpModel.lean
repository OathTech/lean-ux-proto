import Leanux.Proofs.WG.Config.DumpTransport

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual fixed peer-attribute space summed once for every list visit. -/
def multiPeerSpace (peers : PeerId → Peer) (ids : List PeerId) : Nat :=
  (ids.map fun pid => peerFixedSpace (peers pid)).sum

/-- Ordered peer records, including repeated visits and arbitrary endpoints. -/
def multiPeerParts (peers : PeerId → Peer) (ids : List PeerId) : List PeerDumpAttrs :=
  ids.map fun pid => {publicKey := hexKey (peers pid).remoteStatic, attrs := peerFixedAttrs (peers pid)}

/-- Exact completing first callback, retaining the cancelled peer nest when
the device list is empty. No pagination or callback-success assumption is encoded. -/
def multiPeerCall (d : Device) (peers : PeerId → Peer) (ids : List PeerId) : DumpCall :=
  {ret := 0, skb := {room := NLMSG_GOODSIZE - devicePrefixSpace d - multiPeerSpace peers ids, messages := [.data 2 (deviceFixedAttrs d) (if ids.isEmpty then none else some (multiPeerParts peers ids))]}, ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen}

/-- Conservative capacity bound used to fit all peers and a final DONE. -/
theorem multiPeerSpace_bound (peers : PeerId → Peer) (ids : List PeerId) :
    multiPeerSpace peers ids ≤ 168 * ids.length := by
  induction ids with
  | nil => simp [multiPeerSpace]
  | cons pid ids ih =>
    have one := peerFixedSpace_bound (peers pid)
    simp only [multiPeerSpace,List.map_cons,List.sum_cons,List.length_cons] at *
    omega


end Leanux.Proofs.WG.Config
