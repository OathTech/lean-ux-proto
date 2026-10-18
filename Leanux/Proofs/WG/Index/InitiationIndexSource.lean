import Leanux.Proofs.WG.Index.SenderIndexClaims
import Leanux.Proofs.WG.Index.SelectedSendRetirementEffects
import Leanux.Proofs.WG.Index.SelectedSendRetirementSource
import Leanux.Proofs.WG.Index.RetirementWholeBulkSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits Queues.RxCredits.DurableHolders

/-- The selected loan supplies caller positivity and configured identity supplies
its nullable self word. The contracts use the same actual sender run. -/
theorem initiationIndexContract_actual (holders : DurableHolders) (cs : Ledger)
    (paid : Owner) (retired loans : Reservations) :
    InitiationIndexContract holders cs paid retired loans := by
  intro w a result v b pre run
  have safe := pre.2.2.2.2
  have caller := funded_send_handshakeCompatible holders cs paid (retired ++ loans) w
    pre.1 pre.2.2.1 safe.2.1
  have owner := sendHandshakeInitiation_owner_compatible paid.slot
    w a result v b caller run
  have retained := sendHandshakeInitiation_hashSlots_retirement retired paid.slot
    w a result v b ⟨safe.1,safe.2.2⟩ run
  exact ⟨retained.1,fun d device => (owner d device).1,retained.2⟩

/-- The complete after-dead removal pays its selected occurrence and discharges
its retirement root. Every send callback uses the original initiation contract. -/
theorem peerRemoveAfterDead_retirement_actual
    (original : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations) :
    Ensures (peerRemoveAfterDead paid.slot)
      (RetirementWork original cs (paid :: (retired ++ loans)) (paid :: retired))
      (fun _ => RetirementWork original cs (retired ++ loans) retired) :=
  peerRemoveAfterDead_retirement_initiation original cs paid retired loans
    (fun holders selected => initiationIndexContract_actual holders cs selected retired (paid :: loans))

/-- Actual bulk removal retains the prior retirement obligations after both
saved passes and all funded cleanup. No callback contract remains assumed. -/
theorem peerRemoveAll_retirement_actual
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations) :
    Ensures peerRemoveAll
      (fun w => ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
        holders.Funded cs (retired ++ loans) w ∧ StableRx cs w ∧
        (∀ d, w.dev = some d → HashSlotCoverage d) ∧
        (∀ d, w.dev = some d → HashedOwnersCoherent d) ∧
        (∀ d, w.dev = some d → DeadHashedReserved retired d))
      (fun _ => RetirementWork (holders.withoutBase []) cs (retired ++ loans) retired) :=
  peerRemoveAll_retirement_initiation holders cs retired loans
    (fun _ paid _ _ current selected =>
      initiationIndexContract_actual current cs selected _ (paid :: loans))

end Leanux.Proofs.WG.Index
