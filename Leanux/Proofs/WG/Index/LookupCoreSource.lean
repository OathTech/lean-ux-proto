import Leanux.Proofs.WG.Index.LookupCoreClaims
import Leanux.Proofs.WG.Index.ReachedIndexSource
import Leanux.Proofs.WG.Index.RetirementPaymentSource
import Leanux.Proofs.WG.Queues.DeviceBoundary

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do

namespace Reached
/-- Funded payment permits the actual final-reference case. The original paid
head occurrence is consumed; arbitrary remaining loans keep their order and
multiplicity. Empty retirement is an entry fact, not an assumed output. -/
theorem peerPut_funded_core (original : DurableHolders) (cs : Ledger)
    (paid : Owner) (loans : Reservations) :
    Ensures (peerPut (some paid.slot))
      (fun w => DuringWork original cs (paid::loans) w ∧
        ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧ Core w)
      (fun _ w => DuringWork original cs loans w ∧
        ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧ Core w) := by
  intro w a result v b pre run
  cases result
  have payment := peerPut_retirement_payment original cs paid [] loans w v a b
    pre.2.1 pre.2.2.1 pre.1
    (fun d device => (pre.2.2.2 d device).2.1)
    (fun d device => (pre.2.2.2 d device).2.2.1)
    (fun d device => (pre.2.2.2 d device).2.2.2) run
  have tables := (ensures_iff _ _ _).mpr (peerPut_tables (some paid.slot))
    w a () v b (fun d device => (pre.2.2.2 d device).1) run
  have configured := (hoare_iff_run_ambient _ _ _).mp
    (ConfiguredIdentity.peerPut_preserves (some paid.slot))
      w a () v b pre.2.1 run
  have base := BaseCoherence.transport pre.2.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerPut_view (some paid.slot))
      w a () v b run)
  exact ⟨payment.1,configured,base,fun d device =>
    ⟨tables d device,payment.2.1 d device,payment.2.2.1 d device,payment.2.2.2 d device⟩⟩

/-- A configuration-selected loan cut supplies the same funded payment without
a WorkRemainder premise. The existing account is only packaged and unpackaged;
its payment is the landed original-source contract. -/
theorem peerPut_boundary_core (cs : Ledger) (paid : Owner) (loans : Reservations) :
    Ensures (peerPut (some paid.slot))
      (fun w => DeviceBoundary.Entry cs (paid::loans) w ∧ Core w)
      (fun _ w => DeviceBoundary.Entry cs loans w ∧ Core w) := by
  intro w a result v b pre run
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  have post := peerPut_funded_core holders cs paid loans w a result v b
    ⟨duringWork_initial funded stable,pre.1.2.2,pre.1.2.1,pre.2⟩ run
  obtain ⟨after,_,fundedAfter,stableAfter⟩ := post.1
  exact ⟨⟨⟨after,fundedAfter,stableAfter⟩,post.2.2.1,post.2.1⟩,post.2.2.2⟩
end Reached
end Leanux.Proofs.WG.Index
