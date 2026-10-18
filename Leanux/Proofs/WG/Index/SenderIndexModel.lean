import Leanux.Proofs.WG.Index.CreatorIndexClaims
import Leanux.Proofs.WG.Index.CreatorCompatibleClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise TimerDiscipline Std.Do Leanux.Proofs.Framing
open Queues.RxCredits

abbrev SenderPeerCell := List (Option KeypairId) × Nat × Option PeerId × Nat × Bool
def senderPeerCell (p : Peer) : SenderPeerCell :=
  (clearKeys p,p.refcount,p.handshakeEntryPeer,p.internalId,p.isDead)
abbrev SenderDeviceCell := List IndexEntry × Nat × (KeypairId → Option Keypair) × (PeerId → Option SenderPeerCell)
def senderDeviceCell (d : Device) : SenderDeviceCell :=
  (d.indexTable,d.ifindex,fun kid => d.keypairs[kid]?,fun pid => d.peers[pid]?.map senderPeerCell)

end Leanux.Proofs.WG.Index
