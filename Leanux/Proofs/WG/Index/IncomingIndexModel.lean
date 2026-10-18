import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.RetirementModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

def IncomingIndexDevice (retired : Reservations) (d : Device) : Prop :=
  HashSlotCoverage d ∧ DeadHashedReserved retired d

def IncomingIndexSafe (retired : Reservations) (g : WGWorld) : Prop :=
  ∀ d, g.dev = some d → IncomingIndexDevice retired d

def IncomingIndexHeld (retired : Reservations) (pid : PeerId) (g : WGWorld) : Prop :=
  IncomingIndexSafe retired g ∧
    ∃ d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount
end Leanux.Proofs.WG.Index
