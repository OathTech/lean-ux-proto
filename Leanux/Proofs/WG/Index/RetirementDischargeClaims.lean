import Leanux.Proofs.WG.Index.RetirementDischargeEffects
import Leanux.Proofs.WG.Index.RetirementRetentionClaims
import Leanux.Proofs.WG.Index.HashSlotClearClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- Actual clearing discharges this owner's retirement obligation while
preserving coverage and coherence; all original failures remain possible. -/
theorem keypairsClear_retirement_discharge (paid : Owner) (retired : Reservations) :
    Campaign2.Ensures (keypairsClear paid.slot)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧
        View.RetirementSafe (paid :: retired) s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧
        View.RetirementSafe retired s) := by
  intro w a value v b pre run
  obtain ⟨covered,coherent,d,p,device,resident,empty,_⟩ :=
    keypairsClear_hashSlots_detached paid.slot w a value v b ⟨pre.1,pre.2.1⟩ run
  have reserved := keypairsClear_retirement (paid :: retired) paid.slot w a value v b pre.2.2 run
  refine ⟨covered,coherent,?_⟩
  intro actual found
  have same : actual = d := Option.some.inj (found.symm.trans device)
  subst actual
  apply cleared_retirement_discharge paid retired d (covered d device) (reserved d device)
  intro peer stored
  have equal : peer = p := Option.some.inj (stored.symm.trans resident)
  subst peer
  exact empty

end Leanux.Proofs.WG.Index
