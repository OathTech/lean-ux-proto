import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionCarrierDisposalFrames

/-! Actual removal drains use the final journal's observed send callback.
Native clearing and peer deletion can retire occurrences but cannot create them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
macro "selection_removal_step" : tactic => `(tactic| first
  | (selection_carrier_head Hooks.peerRelease; exact peer_release _)
  | (selection_carrier_head liftWGPrefix; apply state_native; solve | causal_delayed_removal_step)
  | (selection_carrier_head ForIn.forIn; rw [Std.Legacy.Range.forIn_eq_forIn_range']; apply state_forIn)
  | selection_state_step)

theorem sendDrain (upTo : Option PeerId) : StateSafe (sendDrainObserved hooks upTo) :=
  SendCallers.drain_preserves Inv Safe (fun _ _ hi => hi.2) _ _ Selections.flushed_send
    (fun pid => state_combine _ (Delayed.flushed_clear_observed pid)
      (Selections.callback_state (CallbackFrames.flushed_clear_quiet Selections.protected? (fun _ => rfl) pid))) upTo

theorem removeAfter (pid : PeerId) : StateSafe
      (HandshakeSecurity.StagedDisposal.Lifecycle.afterDeadWith liftWGPrefix (sendDrainObserved hooks) hooks.peerRelease pid) := by
  unfold HandshakeSecurity.StagedDisposal.Lifecycle.afterDeadWith timersStopWith
  repeat' first
    | (selection_carrier_head sendDrainObserved; exact sendDrain _)
    | selection_removal_step

theorem remove (peer : Option PeerId) : StateSafe (removeObserved hooks peer) := by
  unfold removeObserved
  unfold HandshakeSecurity.StagedDisposal.Lifecycle.removeWith peerRemoveWith
  repeat' first
    | (selection_carrier_head HandshakeSecurity.StagedDisposal.Lifecycle.afterDeadWith; exact removeAfter _)
    | selection_removal_step
  all_goals simp_all only [Option.some.injEq]
  all_goals first | exact removeAfter _ | contradiction

theorem removeAll :
    StateSafe (removeAllObserved hooks) := by
  unfold removeAllObserved
  unfold HandshakeSecurity.StagedDisposal.Lifecycle.removeAllWith peerRemoveAllWith
  repeat' first
    | (selection_carrier_head HandshakeSecurity.StagedDisposal.Lifecycle.afterDeadWith; exact removeAfter _)
    | selection_removal_step
  all_goals exact state_native _ Delayed.free_allowed

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
