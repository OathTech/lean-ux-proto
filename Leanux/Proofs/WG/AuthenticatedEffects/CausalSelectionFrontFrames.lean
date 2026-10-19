import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionQuiet

/-! The observed front preserves unrelated selection history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
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

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
