import Leanux.Proofs.WG.Queues.BaseCoherenceTraffic

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem base_modify (f : Device → Device)
    (same : ∀d,(f d).peerList=d.peerList ∧ (f d).peerHashtable=d.peerHashtable) :
    SameView BaseCoherence.view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  cases device : w.dev with
  | none => simp [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device]
  | some d => simp [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device,
      (same d).1,(same d).2]


end Leanux.Proofs.WG.Config.OwnerConfiguration
