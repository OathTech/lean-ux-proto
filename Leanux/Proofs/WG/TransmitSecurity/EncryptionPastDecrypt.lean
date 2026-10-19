import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastIngress
import Leanux.Proofs.WG.Queues.TxLiveWorkers

/-! The original decrypt worker and its actual NAPI placements preserve the
supplied historical TX exclusion. This is state transport, not an authentication
claim about packets rejected or accepted by decryption. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Decrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000

private theorem publish (id : SkbId) (state : PacketState) :
    Preserves (Ready past active) (RxWorkers.publishSource id state) := by
  unfold RxWorkers.publishSource
  simp (config := {zeta := false}) only [invariant]
  repeat' encryption_past_ingress_step

theorem packet (pkt : RxPacket) : Preserves (Ready past active) (decryptPacket pkt) := by
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' encryption_past_ingress_step

theorem prepare : Preserves (Ready past active) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head decryptPacket; exact packet _)
    | (allocation_release_head RxWorkers.publishSource; exact publish _ _)
    | encryption_past_ingress_step

/-- The concrete pre-poll, prepare, IRQ tail and post-poll all use their actual
source order; no scheduler or authentication hypothesis is substituted. -/
theorem step : Preserves (fun w : World => Ready past active w.wg)
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind Napi.softirq
  intro _
  apply preserves_bind (PublicationPoll.native_product (Ready past active) _ prepare)
  intro result
  cases result with
  | none => exact preserves_pure false
  | some pid => exact preserves_bind Napi.irqExit fun _ =>
      preserves_bind (PublicationPoll.native_product (Ready past active) _
        (ready_frame (LiveFrontier.peer_put (some pid)) (peer_put (some pid)))) fun _ =>
        preserves_bind Napi.softirq (fun _ => preserves_pure true)

theorem iteration : Preserves (fun w : World => Ready past active w.wg)
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  let P := fun w : World => Ready past active w.wg
  have stepSpec : Preserves P (decryptStep Env.napiSoftirq Env.napiIrqExit) := step
  have need : Preserves P (Env.condResched .decryptWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [decryptIter,workerIter] using [stepSpec,need,ambient]

theorem observed : PrefixPreserves (fun _ w => Ready past active w.wg) (fun _ => True)
    RxHistory.decryptIteration :=
  Napi.observed _ _
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.decryptIteration_appends)
    RxHistory.decryptIteration_erases iteration

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Decrypt
