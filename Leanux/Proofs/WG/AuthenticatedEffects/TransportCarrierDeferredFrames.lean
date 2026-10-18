import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierScheduler
import Leanux.Proofs.WG.Packets.PublicationClear
import Leanux.Proofs.WG.TransmitSecurity.NonceDeferredFrames

/-! Concrete native RX projection frames for deferred timer housekeeping. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity.Driver
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}

theorem delTimer_rx (pid : PeerId) (timer : PeerTimer) :
    SameView RxDisposition.nativeRxStore (delTimer pid timer) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid timer).factor Prod.snd

theorem clearKeys_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (keypairsClear pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationClear.«0».Leanux.Proofs.WG.PublicationFrontier.keypairsClear_geometry) pid).factor Prod.snd

theorem clearHandshake_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (handshakeClear pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationClear.«0».Leanux.Proofs.WG.PublicationFrontier.handshakeClear_geometry) pid).factor Prod.snd

theorem queuedClear_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact SameView.bind (clearHandshake_rx pid) (fun _ => SameView.bind (clearKeys_rx pid)
    (fun _ => RxCredits.peerPut_rxView (some pid)))

theorem flushedClear_rx (pid : PeerId) : SameView RxDisposition.nativeRxStore (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  simp only [hidden]
  repeat' first
    | (snapshot_head queuedExpiredZeroKeyMaterial; exact queuedClear_rx _)
    | (snapshot_head modifyDev; apply modifyDev_rx <;> intro d <;> rfl)
    | solve | transport_native_rx
    | (snapshot_head Bind.bind; apply SameView.bind)
    | keypairs_intro_forall

theorem wg_read : ProductSafe extra origin replay (liftPrefix getWG) :=
  product_storeLift _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductSafe extra origin replay (liftPrefix (modifyWG f)) :=
  product_storeLift _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductSafe extra origin replay (liftPrefix getEnv) := by
  apply product_storeLift
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v run
  cases run
  rfl

theorem product_rx (action : Leanux.M α)
    (frame : SameView (fun w : World => RxDisposition.nativeRxStore w.wg) action) :
    ProductSafe extra origin replay (liftPrefix action) := by
  apply viewLiftPrefix_preserves (fun w : World => RxDisposition.nativeRxStore w.wg)
    (fun _ _ hi => hi.2) _ frame
  intro h w v same hi
  exact ⟨hi.1.sameRx same,hi.2⟩

theorem clearOne : ProductSafe extra origin replay (liftPrefix Env.runOneClearWorker) := by
  apply product_rx
  have wg {α : Type} (a : WG.M α) (ha : SameView RxDisposition.nativeRxStore a) :
      SameView (fun w : World => RxDisposition.nativeRxStore w.wg) (liftWG a) :=
    sameView_liftWG _ _ a ha (by intro w v ambient same; exact same)
  have ambient {α : Type} (a : AmbientM α) :
      SameView (fun w : World => RxDisposition.nativeRxStore w.wg) (monadLift a : Leanux.M α) :=
    fun initial => productAmbient_spec a _ (fun _ _ hi => hi)
  unfold Env.runOneClearWorker
  apply SameView.bind (wg _ (TransportPublication.store_rx _ getDev_sameWGStore))
  intro d
  cases d.clearWorkQueue.head? with
  | none => exact ambient (AmbientM.invariant _)
  | some head =>
    dsimp only
    apply SameView.bind (ambient (AmbientM.peekUnit .clearPeerWorker))
    intro unit
    cases unit <;> dsimp only
    all_goals apply SameView.bind
    · exact SameView.pure _ _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact wg _ (flushedClear_rx pid)
    · exact ambient (AmbientM.resolveUnit _ _ _)
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact wg _ (flushedClear_rx pid)

theorem product_forIn (xs : List α) (init : β) (f : α → β → PrefixM E (ForInStep β))
    (hf : ∀ x b, ProductSafe extra origin replay (f x b)) :
    ProductSafe extra origin replay (forIn xs init f) :=
  PrefixPreserves.forIn xs init f (fun _ _ hi => hi.2) hf

theorem product_range (r : Std.Legacy.Range) (init : β) (f : Nat → β → PrefixM E (ForInStep β))
    (hf : ∀ x b, ProductSafe extra origin replay (f x b)) : ProductSafe extra origin replay (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ init f hf

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
