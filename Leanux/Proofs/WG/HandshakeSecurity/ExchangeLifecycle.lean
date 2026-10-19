import Leanux.Proofs.WG.HandshakeSecurity.ExchangeRemoval
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeLifecycleFrames

/-! Native shutdown and destruction carry exchange receipts across every
direct and nested drain. A device's final deletion makes coherence vacuous,
while the completed exchange history remains recorded. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem down_checked (facts : H1DriverSourceFacts) :
    Preserves (Driver.downObserved ExchangeDriver.hooks) := by
  unfold Driver.downObserved
  rw [show ExchangeDriver.hooks.stagedPurge = (fun pid => liftWGPrefix (purgeStagedPackets pid)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.down_neutral]
  unfold SendExchange.downWith SendExchange.stopWith
  repeat' first
    | (nonce_source_head SendExchange.timersStopWith; exact timers_stop_checked facts _)
    | (nonce_source_head requireNotPending; exact lift _ (fun _ => preserves_pure _))
    | (nonce_source_head purgeStagedPackets; exact lift _ (purge_frame _))
    | (nonce_source_head handshakeClear; exact lift _ (fun h => frame h _ (facts.control.clear _)))
    | (nonce_source_head resetLastSentHandshake; exact lift _ (reset_sent_frame _))
    | (nonce_source_head socketReinit; exact lift _ (fun h => socket_frame h _ (socketReinit_sameSocket _ _)))
    | exchange_removal_step facts

theorem destruct_checked (facts : H1DriverSourceFacts) :
    Preserves (Driver.destructObserved ExchangeDriver.hooks) := by
  change Preserves (Configuration.destructWith liftWGPrefix
    (Driver.removeAllObserved ExchangeDriver.hooks) (liftWGPrefix destructFinishSource))
  unfold Configuration.destructWith
  repeat' first
    | (nonce_source_head Driver.removeAllObserved; exact remove_all_checked facts)
    | (nonce_source_head destructFinishSource; exact lift _ destruct_finish_frame)
    | (nonce_source_head socketReinit; exact lift _ (fun h => socket_frame h _ (socketReinit_sameSocket _ _)))
    | exchange_removal_step facts

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
