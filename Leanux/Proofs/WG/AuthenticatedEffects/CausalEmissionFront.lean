import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDisposal
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionRoutingFrames

/-! Input and staged-disposal observations retain the native front's sent
projection and all prior delivery certificates. They authorize no transmission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
open HandshakeSecurity.StagedConservation

private theorem front_body (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu) :=
  state_observed _ _ (Front.front_erases (Front.observedOps_erases _ _) _ _ _ _)
    (Front.front_appends (Front.observedOps_appends _ _) _ _ _ _)
    (state_quiet_of_frame _ (Front.front_appends (Front.observedOps_appends _ _) _ _ _ _)
      (Front.front_frame (Front.observedOps_frame _ _ contributing? (fun _ => rfl)) _ _ _ _))
    (EmissionFrames.front family addr packets mtu)

theorem front_observed (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front Front.observed
  exact state_bind (state_emit _ rfl) (fun _ =>
    state_receipt _ (front_body family addr packets mtu) _ (fun _ => rfl))

namespace Deliveries
private theorem front_body (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe
      (Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu) :=
  quiet_state_from_frame _ (Front.front_appends (Front.observedOps_appends _ _) _ _ _ _)
    (Front.front_frame (Front.observedOps_frame _ _ delivery? (fun _ => rfl)) _ _ _ _)

theorem front_observed (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front Front.observed
  exact Driver.History.state_bind (emit_quiet _ rfl) (fun _ =>
    receipt_quiet _ (front_body family addr packets mtu) _ (fun _ => rfl))
end Deliveries
end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
