import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptHistory
import Leanux.Proofs.WG.AuthenticatedEffects.CausalStackHistory
import Leanux.Proofs.WG.AuthenticatedEffects.CausalHandshakePairFrames

/-! Input and disposal observations preserve unrelated causal histories. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity.StagedConservation

private theorem front_body (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu) := by
  unfold Front.frontWith Front.selectWith
  simp only [Front.observedOps]
  repeat' first
    | (driver_history_head focusStatePrefix; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _ => True.intro) _)
    | driver_state_history_step

theorem disposal_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front Front.observed
  apply Driver.History.state_bind (emit_quiet (.transmitInput ⟨family,addr,packets,mtu⟩) True.intro)
  intro _
  exact receipt_quiet _ (front_body family addr packets mtu) _ (fun _ => True.intro)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts

namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity.StagedConservation

private theorem front_body (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu) := by
  unfold Front.frontWith Front.selectWith
  simp only [Front.observedOps]
  repeat' first
    | (driver_history_head focusStatePrefix; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) _)
    | driver_state_history_step

theorem disposal_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front Front.observed
  apply Driver.History.state_bind (emit_quiet (.transmitInput ⟨family,addr,packets,mtu⟩) rfl)
  intro _
  exact receipt_quiet _ (front_body family addr packets mtu) _ (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.StackOrigins

namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity HandshakeSecurity.StagedConservation

private theorem front_body (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu) := by
  unfold Front.frontWith Front.selectWith
  simp only [Front.observedOps]
  repeat' first
    | (driver_history_head focusStatePrefix; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) _)
    | driver_state_history_step

theorem disposal_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front Front.observed
  apply Driver.History.state_bind (emit_quiet (.transmitInput ⟨family,addr,packets,mtu⟩) rfl)
  intro _
  exact receipt_quiet _ (front_body family addr packets mtu) _ (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
