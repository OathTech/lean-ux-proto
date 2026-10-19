import Leanux.Proofs.WG.Roaming.Model
import Leanux.Proofs.WG.Index.StagedObservation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingRich
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

abbrev PeerCell (p : Peer) :=
  (p.handshakeState,p.keypairNext,p.keypairPrevious,p.keypairCurrent,
   p.handshakeEntryPeer,p.internalId,p.isDead,p.endpoint.map Roaming.destination,p.presharedKey,p.persistentKeepaliveInterval,p.endpoint)
abbrev KeyCell (k : Keypair) := (k.peer,decide (0 < k.refcount))

def peerMap (w : WGWorld) (pid : PeerId) :=
  (w.dev.bind fun d => d.peers[pid]?).map PeerCell
def keyMap (w : WGWorld) (kid : KeypairId) :=
  (w.dev.bind fun d => d.keypairs[kid]?).map KeyCell
def table (w : WGWorld) := (w.dev.map Device.indexTable).getD []
def HashedLive (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → ∀ e ∈ d.indexTable, ∀ kid, e.owner = .keypair kid →
    ∃ k, d.keypairs[kid]? = some k ∧ 0 < k.refcount

structure Frame (entry current : WGWorld) : Prop where
  legacy : StagingFrame entry current
  tables : ∀ e ∈ table current, e ∈ table entry
  peers : ∀ pid cell, peerMap current pid = some cell → peerMap entry pid = some cell
  keys : ∀ kid cell, keyMap current kid = some cell → keyMap entry kid = some cell
  live : HashedLive entry → HashedLive current

end Leanux.Proofs.WG.Index.StagingRich
