import Leanux.Proofs.WG.Index.HashSlotClearClaims
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceZeroWorkerClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceExpiryClaims
import Leanux.Proofs.WG.Index.FlushSource
import Leanux.Proofs.WG.Noise.ClearWorkerClaims
import Leanux.Proofs.WG.Keypairs.MaterialOrigin

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Handshake removal and zeroing change no covered key or key slot. -/
theorem expiryZeroDevice_hashSlotCoverage (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (covered : HashSlotCoverage d) :
    HashSlotCoverage (Config.expiryZeroDevice d pid p) := by
  let removed : Device := {d with indexTable := removeOwner (.handshake pid) d.indexTable}
  exact hashSlotCoverage_peerWrite removed pid p (Config.zeroedHandshake p)
    resident rfl (hashSlotCoverage_remove d (.handshake pid) covered)

end Leanux.Proofs.WG.Index
