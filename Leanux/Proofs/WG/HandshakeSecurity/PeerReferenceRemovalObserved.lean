import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceConfiguration

/-! Every removal drain executes the same exchange-producing send callback,
including the drain inside timersStop. Neither native queue guards nor ordinary
result erasure are used to discard a reachable callback. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 200000
set_option pp.structureInstances false

theorem range_loop {β : Type} (r : Std.Legacy.Range) (init : β)
    (body : Nat → β → WGPrefix Exchange.Event (ForInStep β))
    (safe : ∀ x b, Observed (body x b)) : Observed (forIn r init body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact loop _ init body safe

macro "peer_reference_removal_step" : tactic => `(tactic| first
  | unfold Observed
  | unfold StatePrefixPreserves
  | maintenance_join_let
  | maintenance_join_use
  | (nonce_source_head getDev; exact lift _ (store getDev_sameWGStore))
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (nonce_source_head modifyDev; exact lift _ (modify_device _ (fun _ => rfl)))
  | (nonce_source_head peerPut; exact lift _ (peer_put _))
  | (nonce_source_head peerMakeDead; exact lift _ (make_dead _))
  | (nonce_source_head WG.free; exact lift _ free_ips)
  | (nonce_source_head delTimer; exact lift _ (del_timer _ _))
  | (nonce_source_head keypairsClear; exact lift _ (clear_keys _))
  | (nonce_source_head runFlushedClearWork; exact lift _ (flushed_clear _))
  | (nonce_source_head Driver.Hooks.flushedSend; exact flushed_observed _)
  | (first | nonce_source_head branch | nonce_source_head invariant | nonce_source_head unsupported
           | nonce_source_head peekUnit | nonce_source_head resolveUnit | nonce_source_head getAmbient
           | nonce_source_head throw
     exact ambient _)
  | (first | nonce_source_head Pure.pure | nonce_source_head pure
     exact pure _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head ForIn.forIn; first | apply range_loop | apply loop)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | maintenance_reduce_match
  | (with_reducible split))

theorem drain_observed (upTo : Option PeerId) :
    Observed (Driver.sendDrainObserved ExchangeDriver.hooks upTo) := by
  unfold Driver.sendDrainObserved SendExchange.drainWith
  repeat' peer_reference_removal_step

theorem timers_stop_observed (pid : PeerId) :
    Observed (SendExchange.timersStopWith liftWGPrefix
      (Driver.sendDrainObserved ExchangeDriver.hooks) pid) := by
  unfold SendExchange.timersStopWith
  repeat' first
    | (nonce_source_head Driver.sendDrainObserved; exact drain_observed _)
    | peer_reference_removal_step

theorem after_dead_observed (pid : PeerId) :
    Observed (SendExchange.afterDeadWith liftWGPrefix
      (Driver.sendDrainObserved ExchangeDriver.hooks) pid) := by
  unfold SendExchange.afterDeadWith
  repeat' first
    | (nonce_source_head Driver.sendDrainObserved; exact drain_observed _)
    | (nonce_source_head SendExchange.timersStopWith; exact timers_stop_observed _)
    | peer_reference_removal_step

theorem remove_observed (peer : Option PeerId) :
    Observed (Driver.removeObserved ExchangeDriver.hooks peer) := by
  unfold Driver.removeObserved SendExchange.removeWith Configuration.peerRemoveWith
  repeat' first
    | (nonce_source_head SendExchange.afterDeadWith; exact after_dead_observed _)
    | peer_reference_removal_step

theorem remove_all_observed :
    Observed (Driver.removeAllObserved ExchangeDriver.hooks) := by
  unfold Driver.removeAllObserved SendExchange.removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | (nonce_source_head SendExchange.afterDeadWith; exact after_dead_observed _)
    | peer_reference_removal_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
