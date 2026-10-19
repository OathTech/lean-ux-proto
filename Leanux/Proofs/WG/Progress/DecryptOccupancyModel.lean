import Leanux.Proofs.WG.Progress.ActivationExitModel
import Leanux.Proofs.WG.Queues.RingSteps

/-! Coherent physical decrypt rings and the exclusion of the activation's own
occupancy-exhaustion branch. This model makes no callback termination claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DecryptOccupancy
open Leanux Leanux.WG Leanux.Proofs.WG.Queues

def cell (s : Campaign2.Product.Snapshot) : Option (Nat × PtrRing SkbId) :=
  s.wg.device.map fun d => (d.ifindex,d.decryptQueue)

def Rep (deviceIndex capacity batch : Nat) (live : List SkbId)
    (s : Campaign2.Product.Snapshot) : Prop :=
  ∃ tail stale, Ring.Bounds capacity tail stale live ∧
    cell s = some (deviceIndex,Ring.ringOf capacity batch tail stale live)

def NoExhaustion : ActivationExitAudit Campaign2.Product.Snapshot → Prop
  | .occupancyError _ | .refillsError .. => False
  | .ran _ _ _ (.exhausted ..) => False
  | .ran _ _ _ _ => True


end Leanux.Proofs.WG.Progress.DecryptOccupancy
