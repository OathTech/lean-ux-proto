import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverTimers

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins

theorem carrier_flushed_send (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (runFlushedSendWork pid) :=
  carrier_join confirmed (ConfiguredRemoval.flushedSend pid) (flushedSend_native pid confirmed)

theorem carrier_flushed_clear (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (runFlushedClearWork pid) :=
  carrier_join confirmed (ConfiguredRemoval.flushedClear pid) (flushedClear_native H1 pid confirmed)

theorem carrier_send_one (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.runOneSendWorker := by
  unfold Env.runOneSendWorker
  apply preserves_bind (PublicationPoll.native_product _ _ (carrier_store getDev_sameWGStore confirmed))
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
      exact PublicationPoll.native_product _ _ (carrier_flushed_send pid confirmed)
    · exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (carrier_flushed_send pid confirmed)

theorem carrier_clear_one (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) Env.runOneClearWorker := by
  unfold Env.runOneClearWorker
  apply preserves_bind (PublicationPoll.native_product _ _ (carrier_store getDev_sameWGStore confirmed))
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
      exact PublicationPoll.native_product _ _ (carrier_flushed_clear H1 pid confirmed)
    · exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (carrier_flushed_clear H1 pid confirmed)

theorem wg_read : ProductPreserves (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductPreserves (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductPreserves (liftPrefix getEnv) := by
  apply product_lift
  intro confirmed
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run
  exact hi

theorem send_one : ProductPreserves (liftPrefix Env.runOneSendWorker) :=
  product_lift _ carrier_send_one

theorem clear_one (H1 : H1ResponderCurrentEdges) : ProductPreserves (liftPrefix Env.runOneClearWorker) :=
  product_lift _ (carrier_clear_one H1)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
