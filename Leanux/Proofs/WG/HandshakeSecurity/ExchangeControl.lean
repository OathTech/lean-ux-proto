import Leanux.Proofs.WG.HandshakeSecurity.ExchangeH1ControlFrames

/-! Committed queued-send and clear dispatch share the actual native dequeue
sources. Timer callbacks preserve history without manufacturing exchanges. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000

theorem clear_worker_frame (frames : H1ControlTagFrames) (pid : PeerId) (h : List Event) :
    Framing.Preserves (StateInv h) (queuedExpiredZeroKeyMaterial pid) :=
  preserves_bind (frame h _ (frames.clear pid)) (fun _ =>
    preserves_bind (frame_tag h _ (frames.clearKeys pid)) (fun _ => peer_put (some pid) h))

theorem flushed_clear_frame (frames : H1ControlTagFrames) (pid : PeerId) (h : List Event) :
    Framing.Preserves (StateInv h) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  apply preserves_bind (modify_device (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl) h)
  intro _
  apply preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStart .clearPeerWorker)) _)
  intro _
  apply preserves_bind (clear_worker_frame frames pid h)
  intro _
  exact preserves_bind (hoare_liftAmbient (AmbientM.hidden (.sectionStop .clearPeerWorker)) _) (fun _ => preserves_pure _)

theorem clear_one_frame (frames : H1ControlTagFrames) (h : List Event) :
    Framing.Preserves (ProductInv h) Env.runOneClearWorker := by
  unfold Env.runOneClearWorker
  apply preserves_bind (PublicationPoll.native_product _ _ (frame_store h _ getDev_sameWGStore))
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
      exact PublicationPoll.native_product _ _ (flushed_clear_frame frames pid h)
    · exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ hi => hi)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushed_clear_frame frames pid h)

theorem send_one_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames) :
    ProductPreserves (Driver.sendWorkerObserved ExchangeDriver.hooks) := by
  unfold Driver.sendWorkerObserved SendExchange.oneWith
  apply PrefixPreserves.bind
  · apply product_frame
    intro w value v run
    rw [(AuthenticatedEffects.SendWorkCauses.select_member w v value run).1]
    exact Retains.refl _
  · intro pid
    exact product_state (flushed_checked H1 frames pid)

theorem timer_checked (frames : H1ControlTagFrames) (pid : PeerId) (timer : PeerTimer) :
    Preserves (Driver.timerObserved ExchangeDriver.hooks pid timer) := by
  rw [ExchangeDriver.timer_lift]
  exact lift _ (fun h => frame h _ (frames.timer pid timer))

theorem wg_read : ProductPreserves (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductPreserves (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductPreserves (liftPrefix getEnv) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w value v hi run
  cases run
  exact hi

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
