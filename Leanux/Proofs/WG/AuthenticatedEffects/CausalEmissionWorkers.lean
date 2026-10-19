import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionEncryption
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCompletion

/-! Every actual packet and handshake worker iteration retains ordered socket
append receipts across its native softirq and rescheduling callback cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity Queues

theorem cond_resched (worker : Worker) : ProductSafe (liftPrefix (Env.condResched worker)) := by
  apply product_native
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [Env.condResched,peekHiddenSite,hidden] using [ambient]

theorem resched (worker : Worker) (site : Decision) : ProductSafe (Driver.reschedObserved worker site) := by
  unfold Driver.reschedObserved
  exact product_bind (cond_resched worker) (fun yes => product_ambient (AmbientM.branch site yes))

theorem encrypt_tail (item : Option (List SkbId)) : ProductSafe (Driver.encryptTailObserved hooks item) :=
  workerIterPrefix_preserves .encryptWorker none (fun _ _ _ => True.intro) (encrypt item)
    (resched .encryptWorker .encWorkerNeedResched)

theorem encrypt_iter : ProductSafe (Driver.encryptIterObserved hooks) :=
  product_bind poll (fun item => product_bind softirq (fun _ => encrypt_tail item))

theorem tx_iter (pid : PeerId) : ProductSafe (Driver.txIterObserved hooks pid) :=
  workerIterPrefix_preserves .txWorker (some pid) (fun _ _ _ => True.intro) (transmit pid)
    (resched .txWorker .txNeedResched)

theorem decrypt_step : ProductSafe (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply product_bind softirq
  intro _
  apply product_bind decrypt_prepare
  intro peer
  cases peer with
  | none => exact product_pure _
  | some pid =>
    apply product_bind irq_exit
    intro _
    apply product_bind (product_state (peer_release (some pid)))
    intro _
    exact product_bind softirq (fun _ => product_pure _)

theorem decrypt_iter : ProductSafe (Driver.decryptIterObserved hooks) :=
  workerIterPrefix_preserves .decryptWorker none (fun _ _ _ => True.intro) decrypt_step
    (resched .decryptWorker .decWorkerNeedResched)

theorem receive_iter : ProductSafe (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves .receiveWorker none (fun _ _ _ => True.intro) (product_state handshake_worker)
    (cond_resched .receiveWorker)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
