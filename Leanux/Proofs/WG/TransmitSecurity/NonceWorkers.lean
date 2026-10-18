import Leanux.Proofs.WG.TransmitSecurity.NonceWorkerFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceHandshakeSafety
import Leanux.Proofs.WG.Queues.SourceScheduler

/-! Actual draining-worker iterations, observing nonce reservations in their
native receive, NAPI and handshake callbacks. Consistency trials are handled
separately by the source scheduler and do not represent committed sends. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues


def reschedObserved (worker : Worker) (site : Decision) : PrefixM Allocation Bool := do
  let yes ← liftPrefix (Env.condResched worker)
  liftPrefix (branch site yes)

theorem reschedObserved_erases (worker : Worker) (site : Decision) :
    ErasesPrefix (reschedObserved worker site)
      (do branch site (← Env.condResched worker)) :=
  erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _)

theorem reschedObserved_safe (worker : Worker) (site : Decision) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (reschedObserved worker site) :=
  PrefixPreserves.bind (Frames.resched worker) (fun _ => Frames.product_ambient _)

def encryptTailObserved (item : Option (List SkbId)) : PrefixM Allocation IterResult :=
  workerIterPrefix .encryptWorker none (liftPrefix (RxWorkers.encryptStepTailSource item))
    (reschedObserved .encryptWorker .encWorkerNeedResched)

def encryptIterObserved : PrefixM Allocation IterResult := do
  let item ← liftPrefix (liftWG TxRing.pollSource)
  softirqObserved
  encryptTailObserved item

theorem encryptIterObserved_erases : ErasesPrefix encryptIterObserved
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro item
  apply erasesPrefix_bind softirqObserved_erases
  intro _
  exact workerIterPrefix_erases _ _ (erasesPrefix_lift _) (reschedObserved_erases _ _)

theorem encryptIterObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup encryptIterObserved := by
  apply PrefixPreserves.bind (Frames.product_frame Frames.tx_ring)
  intro item
  apply PrefixPreserves.bind softirqObserved_safe
  intro _
  exact workerIterPrefix_preserves _ _ (fun _ _ hi => hi.nodup)
    (Frames.product_lift (Frames.encrypt_step_tail item)) (reschedObserved_safe _ _)

def txIterObserved (pid : PeerId) : PrefixM Allocation IterResult :=
  workerIterPrefix .txWorker (some pid) (liftPrefix (liftWG (txStep pid)))
    (reschedObserved .txWorker .txNeedResched)

theorem txIterObserved_erases (pid : PeerId) : ErasesPrefix (txIterObserved pid)
    (txIter pid (Env.condResched .txWorker)) :=
  workerIterPrefix_erases _ _ (erasesPrefix_lift _) (reschedObserved_erases _ _)

theorem txIterObserved_safe (pid : PeerId) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (txIterObserved pid) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.nodup)
    (Frames.product_native (Frames.tx_step pid)) (reschedObserved_safe _ _)

def decryptStepObserved : PrefixM Allocation Bool :=
  RxWorkers.decryptWith (liftPrefix (liftWG RxWorkers.prepareSource))
    (fun pid => liftPrefix (liftWG (peerPut (some pid)))) softirqObserved irqExitObserved

theorem decryptStepObserved_erases : ErasesPrefix decryptStepObserved
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold decryptStepObserved RxWorkers.decryptWith RxWorkers.decryptSource
  repeat' first
    | exact softirqObserved_erases
    | exact irqExitObserved_erases
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem decryptStepObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup decryptStepObserved := by
  unfold decryptStepObserved RxWorkers.decryptWith
  apply PrefixPreserves.bind softirqObserved_safe
  intro _
  apply PrefixPreserves.bind (Frames.product_native Frames.rx_prepare)
  intro item
  cases item with
  | none => exact PrefixPreserves.pure (fun _ _ hi => hi.nodup) _
  | some pid =>
    apply PrefixPreserves.bind irqExitObserved_safe
    intro _
    apply PrefixPreserves.bind (Frames.product_frame (Frames.peerPut _))
    intro _
    apply PrefixPreserves.bind softirqObserved_safe
    intro _
    exact PrefixPreserves.pure (fun _ _ hi => hi.nodup) _

def decryptIterObserved : PrefixM Allocation IterResult :=
  workerIterPrefix .decryptWorker none decryptStepObserved
    (reschedObserved .decryptWorker .decWorkerNeedResched)

theorem decryptIterObserved_erases : ErasesPrefix decryptIterObserved
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  workerIterPrefix_erases _ _ decryptStepObserved_erases (reschedObserved_erases _ _)

theorem decryptIterObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup decryptIterObserved :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.nodup)
    decryptStepObserved_safe (reschedObserved_safe _ _)

def receiveIterObserved : PrefixM Allocation IterResult :=
  workerIterPrefix .receiveWorker none (liftWGObserver Handshake.observed)
    (liftPrefix (Env.condResched .receiveWorker))

theorem receiveIterObserved_erases : ErasesPrefix receiveIterObserved
    (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) :=
  workerIterPrefix_erases _ _ (liftWGObserver_erases Handshake.erases) (erasesPrefix_lift _)

theorem receiveIterObserved_safe :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup receiveIterObserved :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.nodup)
    Handshake.safe.liftWGObserver (Frames.resched _)

end Leanux.Proofs.WG.TransmitSecurity.Nonce
