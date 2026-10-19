import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceDeferredFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins

theorem native_send_one :
    Framing.Preserves (fun w : World => Inv w.wg) Env.runOneSendWorker := by
  unfold Env.runOneSendWorker
  apply preserves_bind (PublicationPoll.native_product _ _ (store getDev_sameWGStore))
  intro d
  cases d.sendWorkQueue.head? with
  | none => exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi)
  | some head =>
    dsimp only
    apply preserves_bind (productAmbient_spec (AmbientM.peekUnit .sendWorker) _ (fun _ _ hi => hi))
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed_send pid)
    · exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed_send pid)

theorem native_clear_one :
    Framing.Preserves (fun w : World => Inv w.wg) Env.runOneClearWorker := by
  unfold Env.runOneClearWorker
  apply preserves_bind (PublicationPoll.native_product _ _ (store getDev_sameWGStore))
  intro d
  cases d.clearWorkQueue.head? with
  | none => exact productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi)
  | some head =>
    dsimp only
    apply preserves_bind (productAmbient_spec (AmbientM.peekUnit .clearPeerWorker) _ (fun _ _ hi => hi))
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed_clear pid)
    · exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed_clear pid)

theorem wg_read : ProductPreserves (E := E) (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductPreserves (E := E) (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductPreserves (E := E) (liftPrefix getEnv) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run
  exact hi

theorem native_send_one_observed : ProductPreserves (E := E) (liftPrefix Env.runOneSendWorker) :=
  product_lift _ native_send_one

theorem clear_one : ProductPreserves (E := E) (liftPrefix Env.runOneClearWorker) :=
  product_lift _ (native_clear_one)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
