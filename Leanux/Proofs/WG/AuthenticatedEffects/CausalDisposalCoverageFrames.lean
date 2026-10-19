import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageScopes

/-! Transmit entry and disposal records do not themselves authorize effects. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem staged_purge (pid : PeerId) : StateAt frames (CausalJournal.stagedPurge pid) :=
  state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) (fun _ h => h.elim) _

theorem peer_release (peer : Option PeerId) : StateAt frames (CausalJournal.peerRelease peer) :=
  state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) (fun _ h => h.elim) _

theorem input_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateAt frames (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front Front.observed
  apply state_bind (state_emit (.transmitInput ⟨family,addr,packets,mtu⟩) rfl (fun h => h.elim))
  intro _
  apply state_receipt _ _ (fun run => .old (.routed family addr packets mtu run)) (fun _ => rfl) (fun _ h => h.elim)
  unfold Front.frontWith Front.selectWith
  simp only [Front.observedOps]
  repeat' first
    | (coverage_head focusStatePrefix; exact state_focus Event.stagedDisposal stagedDisposal?
        (fun _ => rfl) (fun _ h => h.elim) _)
    | coverage_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
