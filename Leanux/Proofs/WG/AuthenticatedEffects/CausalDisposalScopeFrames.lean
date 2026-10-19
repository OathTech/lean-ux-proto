import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeFlow
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors

/-! New disposal records preserve the actual lexical scope, including Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeSecurity.StagedConservation

theorem staged_purge (pid : PeerId) : StateSafe (CausalJournal.stagedPurge pid) :=
  state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) _

theorem peer_release (peer : Option PeerId) : StateSafe (CausalJournal.peerRelease peer) :=
  state_focus Event.stagedDisposal stagedDisposal? (fun _ => rfl) _

theorem callback_state (quiet : CallbackQuiet.StateQuiet scope? body) : StateSafe body :=
  CausalScope.state_balanced_frame scope? body quiet.1 quiet.2

theorem callback_product (quiet : CallbackQuiet.ProductQuiet scope? body) : ProductSafe body :=
  CausalScope.product_balanced_frame scope? body quiet.1 quiet.2

theorem selection (pid : PeerId) : StateSafe (CausalJournal.selection pid) :=
  callback_state (CallbackQuiet.selection scope? (fun _ => rfl) (fun _ _ => rfl) pid)

theorem restore (pid : PeerId) (packets : List Packet) : StateSafe (CausalJournal.stagedRestore pid packets) :=
  callback_state (CallbackQuiet.restore scope? (fun _ => rfl) pid packets)

theorem create (pid : PeerId) (items : List SkbId) : StateSafe (CausalJournal.create pid items) :=
  callback_state (CallbackQuiet.create scope? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid items)

theorem encrypt (items : Option (List SkbId)) : ProductSafe (CausalJournal.encrypt items) :=
  callback_product (CallbackQuiet.encrypt scope? (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) items)

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
