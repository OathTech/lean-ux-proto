import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeFlow

/-! New disposal records preserve the actual lexical scope, including Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeSecurity.StagedConservation

theorem staged_purge (pid : PeerId) : StateSafe (CausalJournal.stagedPurge pid) :=
  state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) _

theorem peer_release (peer : Option PeerId) : StateSafe (CausalJournal.peerRelease peer) :=
  state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) _

theorem input_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front Front.observed
  apply state_bind (state_emit _ rfl)
  intro _
  apply state_receipt _ _ _ (fun _ => rfl)
  exact CausalScope.state_balanced_frame scope? _
    (Front.front_appends (Front.observedOps_appends _ _) _ _ _ _)
    (Front.front_frame (Front.observedOps_frame Event.stagedDisposal stagedDisposal? scope? (fun _ => rfl)) _ _ _ _)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
