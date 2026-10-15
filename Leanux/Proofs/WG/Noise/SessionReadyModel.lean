import Leanux.Proofs.WG.Noise.SessionModel

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Static release readiness after the allocator's actual insertion. This
retains allocation-ID aliases and accounts for an overwritten reference count. -/
def SessionReady (d : Device) (p : Peer) (counter : Nat) : Prop :=
  ClearReady (Index.createdDevice d counter p.handshakeEntryPeer)
    (rotationReleases (rotationPlan (sessionZeroPeer p)
      (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId))

/-- The two records consumed by a successful, armed session allocation and
the following key derivation. Payload validity is stated separately. -/
def sessionReadyRecords (allocation clock : List UInt8) (rest : List HiddenRecord) :
    List HiddenRecord :=
  { site := (HiddenSite.alloc .kzallocKeypair).info.id, bytes := allocation } ::
  { site := HiddenSite.deriveKeysBirthdate.info.id, bytes := clock } :: rest

end Leanux.Proofs.WG.Noise
