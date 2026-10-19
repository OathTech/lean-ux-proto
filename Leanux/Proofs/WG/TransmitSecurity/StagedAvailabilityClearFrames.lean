import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityDeferredFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNativeCallbacks

/-! Native clear work preserves surviving staged availability; observed release
receipts additionally preserve their positional history. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem clear_native (h : List Event) :
    Preserves (fun w : World => Inv h w.wg) Env.runOneClearWorker := by
  let P := fun w : World => Inv h w.wg
  change Preserves P _
  have native (pid : PeerId) : Preserves P (liftWG (runFlushedClearWork pid)) :=
    Native.product _ (native_flushed_clear pid)
  have getter : Preserves P (liftWG getDev) := Native.product _ (Native.store getDev_sameWGStore)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  unfold Env.runOneClearWorker
  apply preserves_bind getter
  intro d
  cases d.clearWorkQueue.head? with
  | none => exact ambient (AmbientM.invariant _)
  | some head =>
    dsimp only
    apply preserves_bind (ambient (AmbientM.peekUnit .clearPeerWorker))
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact native pid
    · exact ambient (AmbientM.resolveUnit _ _ _)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact native pid

theorem clear_worker : ProductSafe (Driver.clearWorkerObserved hooks) := by
  have quiet := CallbackFrames.clear_worker_quiet allocation? (fun _ => rfl)
  exact product_quiet quiet.1 quiet.2 CallbackFrames.clear_worker_erases clear_native

theorem flushed_clear (pid : PeerId) : StateSafe
    (RetirementSecurity.NestedPeerRelease.flushedClearWith (Driver.nestedOps hooks) pid) := by
  have quiet := CallbackFrames.flushed_clear_quiet allocation? (fun _ => rfl) pid
  exact state_quiet quiet.1 quiet.2 (CallbackFrames.flushed_clear_erases pid)
    (fun _ => native_flushed_clear pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
