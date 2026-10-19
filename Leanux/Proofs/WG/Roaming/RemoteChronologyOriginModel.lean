import Leanux.Proofs.WG.Roaming.RemoteProvenanceModel
import Leanux.Proofs.WG.Roaming.RemoteChronologyModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

/-- An actual endpoint setter's journal position and projected explanation. -/
structure LatestOrigin where
  position : Nat
  origin : RemoteProvenance.Origin

end Leanux.Proofs.WG.Roaming.RemoteChronology
