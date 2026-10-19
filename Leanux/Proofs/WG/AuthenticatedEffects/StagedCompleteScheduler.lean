import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSchedulerFrames

/-! Actual worker iterations and scheduler trials compose paired packet
accounting. Each actual worker contract is explicit at this local boundary;
no copied trial is treated as a committed packet-history event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem encrypt_tail (item : Option (List SkbId)) (encrypted : Checked (hooks.encrypt item)) :
    Checked (Driver.encryptTailObserved hooks item) :=
  workerIterPrefix_preserves .encryptWorker none carrier_safe encrypted
    (resched .encryptWorker .encWorkerNeedResched)

theorem encrypt_iter (polled : Checked hooks.poll) (softirq : Checked (Driver.softirqObserved hooks))
    (encrypted : ∀ item, Checked (hooks.encrypt item)) : Checked (Driver.encryptIterObserved hooks) :=
  bind_checked polled (fun item => bind_checked softirq (fun _ => encrypt_tail item (encrypted item)))

theorem tx_iter (pid : PeerId) (transmitted : Checked (hooks.transmit pid)) :
    Checked (Driver.txIterObserved hooks pid) :=
  workerIterPrefix_preserves .txWorker (some pid) carrier_safe transmitted
    (resched .txWorker .txNeedResched)

theorem decrypt_step (prepared : Checked hooks.prepare)
    (released : ∀ pid, Checked (liftWGObserver (hooks.peerRelease (some pid))))
    (softirq : Checked (Driver.softirqObserved hooks)) (irq : Checked (Driver.irqExitObserved hooks)) :
    Checked (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply bind_checked softirq
  intro ignored
  apply bind_checked prepared
  intro peer
  cases peer with
  | none => exact pure_checked _
  | some pid => exact bind_checked irq (fun _ => bind_checked (released pid)
      (fun _ => bind_checked softirq (fun _ => pure_checked _)))

theorem decrypt_iter (step : Checked (Driver.decryptStepObserved hooks)) :
    Checked (Driver.decryptIterObserved hooks) :=
  workerIterPrefix_preserves .decryptWorker none carrier_safe step
    (resched .decryptWorker .decWorkerNeedResched)

theorem receive_iter (received : Checked (liftWGObserver (Driver.handshakeObserved hooks))) :
    Checked (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves .receiveWorker none carrier_safe received
    (product_store _ (condResched_sameKernel .receiveWorker))

variable (encrypts : Checked (Driver.encryptIterObserved hooks))
variable (decrypts : Checked (Driver.decryptIterObserved hooks))
variable (receives : Checked (Driver.receiveIterObserved hooks))
variable (transmits : ∀ pid, Checked (Driver.txIterObserved hooks pid))
include encrypts

theorem crypt_ahead (pid : PeerId) : Checked (Driver.cryptAheadObserved hooks pid) := by
  unfold Driver.cryptAheadObserved
  repeat' first
    | (complete_product_head Driver.encryptIterObserved; exact encrypts)
    | solve | complete_scheduler_native
    | complete_product_step

include decrypts receives transmits

theorem iteration (activation : Activation) : Checked (Driver.iterationObserved hooks activation) := by
  unfold Driver.iterationObserved
  repeat' first
    | (complete_product_head Driver.encryptIterObserved; exact encrypts)
    | (complete_product_head Driver.decryptIterObserved; exact decrypts)
    | (complete_product_head Driver.receiveIterObserved; exact receives)
    | (complete_product_head Driver.txIterObserved; exact transmits _)
    | (complete_product_head Driver.cryptAheadObserved; exact crypt_ahead encrypts _)
    | solve | complete_scheduler_native
    | complete_product_step

theorem schedule (softirq : Checked (Driver.softirqObserved hooks)) (stack : Option Worker) :
    Checked (Driver.scheduleObserved hooks stack) := by
  apply SourceScheduler.schedule_preserves (I := Carrier) carrier_safe stable
  · intro pid
    exact wg _ (work_queue (·.erase pid))
  · exact iteration encrypts decrypts receives transmits
  · exact softirq

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
