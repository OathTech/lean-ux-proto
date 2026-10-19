import Leanux.Proofs.WG.AuthenticatedEffects.CausalDisposalCoverageFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoveragePoll
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageCompletion

/-! The same native worker and scheduler callbacks carry positional coverage.
Only the real receive/completion/handshake scopes supply nonempty contexts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem softirq : ProductAt frames (Driver.softirqObserved hooks) :=
  RxNapi.softirq_preserves (I := fun h _ => Inv frames h) (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) (product_state _ (state_lift _)) native_poll

theorem inline_poll : ProductAt frames (Driver.inlinePollObserved hooks) :=
  RxNapi.inline_preserves (I := fun h _ => Inv frames h) (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) (product_state _ (state_lift _)) native_poll

theorem irq_exit : ProductAt frames (Driver.irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (I := fun h _ => Inv frames h) (S := Safe) (fun _ _ ready => ready.1)
    (fun _ _ _ _ ready => ready) (product_state _ (state_lift _)) softirq

theorem resched (worker : Worker) (site : Decision) : ProductAt frames (Driver.reschedObserved worker site) :=
  product_bind (product_lift _) (fun _ => product_lift _)

theorem encrypt_tail (item : Option (List SkbId)) : ProductAt frames (Driver.encryptTailObserved hooks item) :=
  workerIterPrefix_preserves .encryptWorker none (fun _ _ ready => ready.1)
    (encrypt item) (resched .encryptWorker .encWorkerNeedResched)

theorem encrypt_iter : ProductAt frames (Driver.encryptIterObserved hooks) :=
  product_bind poll (fun item => product_bind softirq (fun _ => encrypt_tail item))

theorem tx_iter (pid : PeerId) : ProductAt frames (Driver.txIterObserved hooks pid) :=
  workerIterPrefix_preserves .txWorker (some pid) (fun _ _ ready => ready.1)
    (transmit pid) (resched .txWorker .txNeedResched)

theorem decrypt_step : ProductAt frames (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  repeat' first
    | (coverage_head Driver.Hooks.peerRelease; exact product_state _ (peer_release _))
    | (coverage_head Driver.Hooks.prepare; exact prepare)
    | (coverage_head Driver.softirqObserved; exact softirq)
    | (coverage_head Driver.irqExitObserved; exact irq_exit)
    | coverage_product_step

theorem decrypt_iter : ProductAt frames (Driver.decryptIterObserved hooks) :=
  workerIterPrefix_preserves .decryptWorker none (fun _ _ ready => ready.1)
    decrypt_step (resched .decryptWorker .decWorkerNeedResched)

theorem receive_iter : ProductAt frames (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves .receiveWorker none (fun _ _ ready => ready.1)
    (product_state _ handshake_worker) (product_lift _)

theorem crypt_ahead (pid : PeerId) : ProductAt frames (Driver.cryptAheadObserved hooks pid) := by
  unfold Driver.cryptAheadObserved
  repeat' first
    | (coverage_head Driver.encryptIterObserved; exact encrypt_iter)
    | coverage_product_step

theorem iteration (activation : Activation) : ProductAt frames (Driver.iterationObserved hooks activation) := by
  unfold Driver.iterationObserved
  repeat' first
    | (coverage_head Driver.encryptIterObserved; exact encrypt_iter)
    | (coverage_head Driver.decryptIterObserved; exact decrypt_iter)
    | (coverage_head Driver.receiveIterObserved; exact receive_iter)
    | (coverage_head Driver.txIterObserved; exact tx_iter _)
    | (coverage_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | coverage_product_step

theorem schedule (stack : Option Worker) : ProductAt frames (Driver.scheduleObserved hooks stack) :=
  SourceScheduler.schedule_preserves (I := fun h _ => Inv frames h) (S := Safe)
    (fun _ _ ready => ready.1) (fun _ _ _ _ ready => ready)
    (fun _ => product_lift _) _ _ iteration softirq stack

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
