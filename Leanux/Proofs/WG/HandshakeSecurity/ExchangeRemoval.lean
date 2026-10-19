import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDeferred

/-! Every removal drain executes the same exchange-producing send callback,
including the drain inside timersStop. Neither native queue guards nor ordinary
result erasure are used to discard a reachable callback. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 200000
set_option pp.structureInstances false

theorem loop {α β : Type} (xs : List α) (init : β) (body : α → β → WGPrefix Event (ForInStep β))
    (safe : ∀ x b, Preserves (body x b)) : Preserves (forIn xs init body) :=
  StatePrefixEnsures.forInInvariant xs init body (fun _ h w _ => StateInv h w) Safe
    (fun _ _ _ _ hi => hi.safe) safe

theorem range_loop {β : Type} (r : Std.Legacy.Range) (init : β)
    (body : Nat → β → WGPrefix Event (ForInStep β))
    (safe : ∀ x b, Preserves (body x b)) : Preserves (forIn r init body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact loop _ init body safe

macro "exchange_removal_step " facts:term : tactic => `(tactic| first
  | unfold Preserves
  | unfold StatePrefixPreserves
  | maintenance_join_let
  | maintenance_join_use
  | (nonce_source_head getDev; exact lift _ (fun h => frame_store h _ getDev_sameWGStore))
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (nonce_source_head modifyDev; exact lift _ (modify_device _ (fun _ => rfl)))
  | (nonce_source_head peerPut; exact lift _ (peer_put _))
  | (nonce_source_head peerMakeDead; exact lift_tag _ (($facts).control.makeDead _))
  | (nonce_source_head WG.free; exact lift_tag _ ($facts).control.free)
  | (nonce_source_head delTimer; exact lift_tag _ (($facts).handshake.deleteTimer _ _))
  | (nonce_source_head keypairsClear; exact lift_tag _ (($facts).control.clearKeys _))
  | (nonce_source_head runFlushedClearWork; exact lift _ (flushed_clear_frame ($facts).control _))
  | (nonce_source_head Driver.Hooks.flushedSend; exact flushed_checked ($facts).edges ($facts).handshake _)
  | (first | nonce_source_head branch | nonce_source_head invariant | nonce_source_head unsupported
           | nonce_source_head peekUnit | nonce_source_head resolveUnit | nonce_source_head getAmbient
           | nonce_source_head throw
     exact ambient _)
  | (first | nonce_source_head Pure.pure | nonce_source_head pure
     exact pure _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head ForIn.forIn; first | apply range_loop | apply loop)
  | (nonce_source_head ite; apply conditional)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | maintenance_reduce_match
  | (with_reducible split))

theorem drain_checked (facts : H1DriverSourceFacts) (upTo : Option PeerId) :
    Preserves (Driver.sendDrainObserved ExchangeDriver.hooks upTo) := by
  unfold Driver.sendDrainObserved SendExchange.drainWith
  simp only [Driver.flushedClear_lift ExchangeDriver.hooks rfl]
  repeat' exchange_removal_step facts

theorem timers_stop_checked (facts : H1DriverSourceFacts) (pid : PeerId) :
    Preserves (SendExchange.timersStopWith liftWGPrefix
      (Driver.sendDrainObserved ExchangeDriver.hooks) pid) := by
  unfold SendExchange.timersStopWith
  repeat' first
    | (nonce_source_head Driver.sendDrainObserved; exact drain_checked facts _)
    | exchange_removal_step facts

theorem after_dead_checked (facts : H1DriverSourceFacts) (pid : PeerId) :
    Preserves (SendExchange.afterDeadWith liftWGPrefix
      (Driver.sendDrainObserved ExchangeDriver.hooks) pid) := by
  unfold SendExchange.afterDeadWith
  repeat' first
    | (nonce_source_head Driver.sendDrainObserved; exact drain_checked facts _)
    | (nonce_source_head SendExchange.timersStopWith; exact timers_stop_checked facts _)
    | exchange_removal_step facts

theorem remove_checked (facts : H1DriverSourceFacts) (peer : Option PeerId) :
    Preserves (Driver.removeObserved ExchangeDriver.hooks peer) := by
  unfold Driver.removeObserved
  rw [show ExchangeDriver.hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    HandshakeSecurity.StagedDisposal.Lifecycle.remove_neutral]
  unfold SendExchange.removeWith Configuration.peerRemoveWith
  repeat' first
    | (nonce_source_head SendExchange.afterDeadWith; exact after_dead_checked facts _)
    | exchange_removal_step facts

theorem remove_all_checked (facts : H1DriverSourceFacts) :
    Preserves (Driver.removeAllObserved ExchangeDriver.hooks) := by
  unfold Driver.removeAllObserved
  rw [show ExchangeDriver.hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    HandshakeSecurity.StagedDisposal.Lifecycle.removeAll_neutral]
  unfold SendExchange.removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | (nonce_source_head SendExchange.afterDeadWith; exact after_dead_checked facts _)
    | exchange_removal_step facts

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
