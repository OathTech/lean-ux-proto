import Leanux.Proofs.WG.TimerDiscipline.SendDispatchModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

abbrev InitiationArmProbe := Bool × Campaign2.Product.Snapshot × Campaign2.Product.Outcome (Option UInt64 × Campaign2.Product.Snapshot × Nat)

/-- The original send's prefix inspection and its actual return before peerPut. -/
structure InitiationRearmExecution where
  path : Campaign2.Product.Outcome InitiationArmProbe
  beforeRelease : Campaign2.Product.Snapshot

structure SendRearmExecution where
  send : SendWorkerExecution
  arm : InitiationRearmExecution

end Leanux.Proofs.WG.TimerDiscipline
