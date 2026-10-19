import Leanux.Proofs.WG.Queues.HolderStopPhysical
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityScheduler
import Leanux.Proofs.WG.TransmitSecurity.NonceDeferredFrames

/-! Native clear work and timer-loop bookkeeping preserve positional staged
origins. A selected timer's marker only records metadata here; its native
nextDue validity and prior arm are checked by the separate selection contract. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open AuthenticatedEffects AuthenticatedEffects.CausalJournal Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem product_enter (cause : Cause) : ProductSafe (CausalScope.enterPrefix Event.scope cause) := by
  intro w h hi
  have safe := hi.2.emit (quiet_event (event := .scope (.entered ⟨h.length,cause⟩)) rfl)
  exact ⟨[.scope (.entered ⟨h.length,cause⟩)],rfl,safe,hi.1.append (fun _ _ member => no_use (by simp only [List.mem_singleton] at member; subst_vars; rfl)),safe⟩

theorem timer_selected (d : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    ProductSafe (hooks.timerSelected d bound pid timer entry) := by
  intro w h hi
  exact product_bind (product_emit (.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)) rfl)
    (fun _ => product_enter (.timer bound pid timer entry)) w h hi

theorem timer_finished (token : Nat) : ProductSafe (hooks.timerFinished token) := product_emit _ rfl

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

theorem clear_one : ProductSafe (liftPrefix Env.runOneClearWorker) := by
  apply product_lift
  intro h
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

theorem product_range (r : Std.Legacy.Range) (initial : β) (body : Nat → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn r initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ initial body safe

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
