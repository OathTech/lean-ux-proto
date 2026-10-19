import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedScheduler
import Leanux.Proofs.WG.TransmitSecurity.NonceDeferredFrames

/-! Native clear work and timer-loop bookkeeping preserve live delayed
occurrences. A selected timer's marker only records metadata here; its native
nextDue validity and prior arm are checked by the separate selection contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity Queues TimerSlots
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem product_enter (cause : Cause) : ProductSafe (CausalScope.enterPrefix Event.scope cause) := by
  intro w h hi
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,True.intro,hi.append _⟩

theorem timer_selected (d : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    ProductSafe (hooks.timerSelected d bound pid timer entry) := by
  intro w h hi
  exact product_bind (product_emit (.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)))
    (fun _ => product_enter (.timer bound pid timer entry)) w h hi

theorem timer_finished (token : Nat) : ProductSafe (hooks.timerFinished token) := product_emit _

theorem wg_read : ProductSafe (liftPrefix getWG) :=
  product_store_lift _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductSafe (liftPrefix (modifyWG f)) :=
  product_store_lift _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductSafe (liftPrefix getEnv) := by
  apply product_store_lift
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases run
  rfl

private theorem clear_keys (pid : PeerId) : StateSafe (liftWGPrefix (keypairsClear pid)) := by
  apply state_framed
  · intro initial
    unfold keypairsClear
    index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold keypairsClear
    index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
    repeat' send_work_frame_step initial

private theorem clear_handshake (pid : PeerId) : StateSafe (liftWGPrefix (handshakeClear pid)) := by
  apply state_framed
  · intro initial
    unfold handshakeClear handshakeZero
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold handshakeClear handshakeZero
    repeat' send_work_frame_step initial

theorem flushed_clear (pid : PeerId) : StateSafe (liftWGPrefix (runFlushedClearWork pid)) := by
  apply state_native
  intro h
  unfold runFlushedClearWork queuedExpiredZeroKeyMaterial
  simp only [hidden]
  repeat' first
    | (rx_retention_head handshakeClear; exact native_contract _ (clear_handshake _) h)
    | (rx_retention_head keypairsClear; exact native_contract _ (clear_keys _) h)
    | (rx_retention_head peerPut; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by
        apply state_framed
        · intro initial
          apply retained_device
          intro d; rfl
        · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
          intro w a value v b run
          cases run
          simp only [QueuedOccurrences.queue,Option.map_map,Function.comp_def]) h)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem clear_one : ProductSafe (liftPrefix Env.runOneClearWorker) := by
  apply product_native
  intro h
  let P := fun w : World => Inv h w.wg
  change Preserves P _
  have native (pid : PeerId) : Preserves P (liftWG (runFlushedClearWork pid)) :=
    native_product_contract _ (flushed_clear pid) h
  have getter : Preserves P (liftWG getDev) := native_product_contract _ (native_store _ getDev_sameWGStore) h
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

theorem product_range (r : Std.Legacy.Range) (initial : β) (body : Nat → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn r initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ initial body safe

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
