import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedAllowedIps

/-! Actual removal drains use the final journal's observed send callback.
Native clearing and peer deletion can retire occurrences but cannot create them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
macro "causal_delayed_removal_step" : tactic => `(tactic| first
  | (causal_delayed_native_head runFlushedClearWork; exact flushed_clear _)
  | (causal_delayed_native_head keypairsClear; exact clear_keys _)
  | (causal_delayed_native_head delTimer; exact delete _ _)
  | (causal_delayed_native_head peerMakeDead; exact dead _)
  | (causal_delayed_native_head free; exact free_allowed)
  | (first | causal_delayed_native_head peekUnit | causal_delayed_native_head resolveUnit
           | causal_delayed_native_head getAmbient
     apply state_native; intro h
     simp only [peekUnit,resolveUnit,getAmbient]
     exact hoare_liftAmbient _ _)
  | (causal_delayed_head liftWGPrefix; solve | causal_delayed_native)
  | (causal_delayed_head ForIn.forIn; rw [Std.Legacy.Range.forIn_eq_forIn_range']; apply state_forIn)
  | causal_delayed_step)

theorem sendDrain (upTo : Option PeerId) : StateSafe (sendDrainObserved hooks upTo) := by
  unfold sendDrainObserved drainWith
  repeat' first
    | (causal_delayed_head Hooks.flushedSend; exact flushed_send _)
    | causal_delayed_removal_step
  all_goals apply state_native; intro h; apply (hoare_iff_run_ambient _ _ _).mpr; intro w a x v b hi run; cases run; exact hi

theorem removeAfter (pid : PeerId) : StateSafe
      (afterDeadWith liftWGPrefix (sendDrainObserved hooks) pid) := by
  unfold afterDeadWith timersStopWith
  repeat' first
    | (causal_delayed_head sendDrainObserved; exact sendDrain _)
    | causal_delayed_removal_step

theorem remove (peer : Option PeerId) : StateSafe (removeObserved hooks peer) := by
  unfold removeObserved
  rw [show hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.remove_neutral]
  unfold removeWith peerRemoveWith
  repeat' first
    | (causal_delayed_head afterDeadWith; exact removeAfter _)
    | causal_delayed_removal_step
  all_goals simp_all only [Option.some.injEq]
  all_goals first | exact removeAfter _ | contradiction

theorem removeAll :
    StateSafe (removeAllObserved hooks) := by
  unfold removeAllObserved
  rw [show hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.removeAll_neutral]
  unfold removeAllWith peerRemoveAllWith
  repeat' first
    | (causal_delayed_head afterDeadWith; exact removeAfter _)
    | causal_delayed_removal_step
  all_goals exact free_allowed

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
