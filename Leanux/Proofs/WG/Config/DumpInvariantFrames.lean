import Leanux.Proofs.WG.Config.DeviceDumpSource
import Leanux.Proofs.WG.Queues.DumpSockets

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config.DumpInvariant
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-- Only the actual mutable leaves need invariant contracts: references and
netlink sockets. The shared whole-walk frame handles serialization and reads. -/
structure Contracts (P : WGWorld → Prop) where
  stable : ∀ w v, dumpView v = dumpView w → P w → P v
  acquire : ∀ pid, Preserves P (peerGet pid)
  release : ∀ pid, Preserves P (peerPut pid)

variable {P : WGWorld → Prop}

theorem frame (c : Contracts P) {α : Type} (action : WG.M α)
    (same : SameDump action) : Preserves P action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact c.stable w v
    ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run) hi

end Leanux.Proofs.WG.Config.DumpInvariant
