import Leanux.Proofs.WG.Index.IncomingIndexModel
import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.RetirementRetentionEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

theorem incomingIndex_peerWrite (retired : Reservations) (d : Device)
    (pid : PeerId) (p q : Peer) (resident : d.peers[pid]? = some p)
    (slots : clearKeys q = clearKeys p)
    (stamp : q.internalId = p.internalId) (dead : q.isDead = p.isDead)
    (pre : IncomingIndexDevice retired d) :
    IncomingIndexDevice retired {d with peers := d.peers.insert pid q} :=
  ⟨hashSlotCoverage_peerWrite d pid p q resident slots pre.1,
    peerWrite_deadHashedReserved retired d pid p q resident stamp dead pre.2⟩

theorem incomingIndex_acquire (retired : Reservations) (d : Device)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p)
    (pre : IncomingIndexDevice retired d) :
    IncomingIndexDevice retired (acquirePeer d pid p) :=
  incomingIndex_peerWrite retired d pid p _ resident rfl rfl rfl pre

theorem incomingIndex_writeHandshake (retired : Reservations) (d : Device)
    (pid : PeerId) (word : Option PeerId) (pre : IncomingIndexDevice retired d) :
    IncomingIndexDevice retired (writeOwnerWord d (.handshake pid) word) := by
  cases resident : d.peers[pid]? with
  | none => simpa only [writeOwnerWord,resident] using pre
  | some p =>
    simpa only [writeOwnerWord,resident] using
      incomingIndex_peerWrite retired d pid p {p with handshakeEntryPeer := word}
        resident rfl rfl rfl pre
end Leanux.Proofs.WG.Index
