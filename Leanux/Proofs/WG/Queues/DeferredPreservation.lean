import Leanux.Proofs.WG.Queues.DeferredSource
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Configuration.RoutingDeferred
import Leanux.Proofs.WG.Packets.OldRx

/-! Generic invariant composition for the exact deferred sources. The old
atoms are justified by their actual erasure and routing-retention contracts;
committed crypt work remains an explicit product callback. -/
namespace Leanux.Proofs.WG.Queues.RxHistory.DeferredSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes AllowedIps
open SchedulerSource

structure AtomContracts {E : Type} (I : List E → World → Prop) (S : List E → Prop)
    (old : {α : Type} → Obs α → PrefixM E α) : Prop where
  sendOne : PrefixPreserves I S (old (audit runOneSendWorkerAudit))
  clearOne : PrefixPreserves I S (old (audit runOneClearWorkerAudit))
  drained : ∀ what queues, PrefixPreserves I S (old (mixed (requireDrainedPrefix what queues)))
  saved : PrefixPreserves I S (old (audit getDevSavedAudit))
  wheel : ∀ d j, PrefixPreserves I S (old (audit (wheelNextDueAudit d j)))
  stepComplete : ∀ b, PrefixPreserves I S (old (audit (requireStepCompleteAudit b)))
  nothingDue : ∀ j, PrefixPreserves I S (old (audit (requireNothingDueAudit j)))
  timer : ∀ worker pid timer entry prior,
    PrefixPreserves I S (old (audit (timerDispatchAudit worker pid timer entry prior)))
  placeholder : ∀ j, PrefixPreserves I S (old (audit (placeholderTimerPassAudit j)))
  idleDevice : PrefixPreserves I S (old (mixed requireIdleDevicePrefix))
  noCrypt : PrefixPreserves I S (old (audit (liftPrefix Env.requireNoCryptWork)))
  timerWorker : ∀ timer, PrefixPreserves I S (old (audit (liftPrefix (Env.timerWorker timer))))
  advance : ∀ ticks, PrefixPreserves I S (old (audit (advanceAudit ticks)))

variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}

theorem AtomContracts.of_routing (old : {α : Type} → Obs α → PrefixM E α)
    (ho : ∀ {α : Type} (g : Obs α) (a : Leanux.M α), Appends g → ErasesPrefix g a →
      ProductRetainsRoutingCall a → PrefixPreserves I S (old g)) : AtomContracts I S old := by
  have stored {α : Type} (a : Leanux.M α) (frame : SameProductStore a) : ProductRetainsRoutingCall a :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.SchedulerPreservation.«0».Leanux.Proofs.WG.Queues.RxHistory.SchedulerSource.product_routing) a frame
  have audited {α : Type} (g : AuditM α) (a : Leanux.M α)
      (erases : ErasesPrefix g a) (frame : ProductRetainsRoutingCall a) :
      PrefixPreserves I S (old (audit g)) :=
    ho _ a (Appends.focus _ _ _) (audit_erases erases) frame
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact audited _ _ runOneSendWorkerAudit_erases runOneSendWorker_routing
  · exact audited _ _ runOneClearWorkerAudit_erases runOneClearWorker_routing
  · intro what queues
    exact ho _ _ (Appends.focus _ _ _) (mixed_erases (requireDrainedPrefix_erases what queues))
      (ProjectedRetainsRoutingCall.of_same (requireDrained_routing what queues))
  · exact audited _ _ getDevSavedAudit_erases (stored _ (liftWG_sameProductStore _ getDev_sameWGStore))
  · intro d j
    exact audited _ _ (wheelNextDueAudit_erases d j) (stored _ (SameView.pure _ _))
  · intro b
    exact audited _ _ (requireStepCompleteAudit_erases b) (ProjectedRetainsRoutingCall.of_same
      ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames.«0».Leanux.Proofs.WG.AllowedIps.requireStepComplete_routing) b))
  · intro j
    exact audited _ _ (requireNothingDueAudit_erases j) (ProjectedRetainsRoutingCall.of_same
      ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames.«0».Leanux.Proofs.WG.AllowedIps.requireNothingDue_routing) j))
  · intro worker pid timer entry prior
    exact audited _ _ (timerDispatchAudit_erases worker pid timer entry prior)
      ((pinned_const _private.Leanux.Proofs.WG.Configuration.RoutingDeferred.«0».Leanux.Proofs.WG.RoutingPosition.Deferred.timerDispatch_frame) worker pid timer entry prior)
  · intro j
    exact audited _ _ (placeholderTimerPass_erases j)
      ((pinned_const _private.Leanux.Proofs.WG.Configuration.RoutingDeferred.«0».Leanux.Proofs.WG.RoutingPosition.Deferred.placeholder_frame) j)
  · exact ho _ _ (Appends.focus _ _ _) (mixed_erases requireIdleDevicePrefix_erases)
      (ProjectedRetainsRoutingCall.of_same requireIdleDevice_routing)
  · exact audited _ _ (erasesPrefix_lift _) (stored _ requireNoCryptWork_sameKernel)
  · intro timer
    exact audited _ _ (erasesPrefix_lift _) (stored _ (timerWorker_sameKernel timer))
  · intro ticks
    exact audited _ _ (advanceAudit_erases ticks) (stored _ (advance_sameKernel ticks))

macro "deferred_raw_steps" safe:ident store:ident : tactic => `(tactic| first
  | (scheduler_preserve_at getWG
     exact viewLiftPrefix_preserves productStoreView $safe $store
       (fun initial => productGetWG_spec (fun s => s = initial)))
  | (scheduler_preserve_at modifyWG
     exact viewLiftPrefix_preserves productStoreView $safe $store
       (fun initial => productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)))
  | (scheduler_preserve_at Env.deliverSent
     exact viewLiftPrefix_preserves productStoreView $safe $store deliverSent_sameKernel)
  | (scheduler_preserve_at Env.requireNoCryptWork
     exact viewLiftPrefix_preserves productStoreView $safe $store requireNoCryptWork_sameKernel)
  | (scheduler_preserve_at Env.peekNextSite
     exact viewLiftPrefix_preserves productStoreView $safe $store peekNextSite_sameKernel)
  | (scheduler_preserve_at getEnv
     exact viewLiftPrefix_preserves productStoreView $safe $store (by
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w x v hr
       cases hr
       rfl))
  | (scheduler_preserve_at peekSiteU64
     exact viewLiftPrefix_preserves productStoreView $safe $store
       (fun _ => productAmbient_spec (AmbientM.peekSiteU64 _) _ (fun _ _ hi => hi)))
  | (scheduler_preserve_at hiddenJiffies
     exact viewLiftPrefix_preserves productStoreView $safe $store
       (fun _ => productAmbient_spec (AmbientM.hiddenJiffies _) _ (fun _ _ hi => hi)))
  | (scheduler_preserve_at throw
     exact viewLiftPrefix_preserves productStoreView $safe $store (fun _ => hoare_throw _))
  | scheduler_raw_steps $safe $store)

macro "deferred_atom_steps" atoms:ident : tactic => `(tactic| first
  | (scheduler_preserve_at runOneSendWorkerAudit; exact ($atoms).sendOne)
  | (scheduler_preserve_at runOneClearWorkerAudit; exact ($atoms).clearOne)
  | (scheduler_preserve_at requireDrainedPrefix; exact ($atoms).drained _ _)
  | (scheduler_preserve_at getDevSavedAudit; exact ($atoms).saved)
  | (scheduler_preserve_at wheelNextDueAudit; exact ($atoms).wheel _ _)
  | (scheduler_preserve_at requireStepCompleteAudit; exact ($atoms).stepComplete _)
  | (scheduler_preserve_at requireNothingDueAudit; exact ($atoms).nothingDue _)
  | (scheduler_preserve_at timerDispatchAudit; exact ($atoms).timer _ _ _ _ _)
  | (scheduler_preserve_at placeholderTimerPassAudit; exact ($atoms).placeholder _))

theorem crypt_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (schedule : PrefixM E Unit) (hs : PrefixPreserves I S schedule) :
    PrefixPreserves I S (cryptWith schedule) := by
  unfold cryptWith
  exact PrefixPreserves.bind hs (fun _ =>
    viewLiftPrefix_preserves productStoreView safe store deliverSent_sameKernel)


theorem send_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (schedule : PrefixM E Unit) (h_schedule : PrefixPreserves I S schedule)
    : PrefixPreserves I S (sendWith old schedule) := by
  unfold sendWith
  repeat' first
    | (scheduler_preserve_at schedule; exact h_schedule)
    | deferred_atom_steps atoms
    | deferred_raw_steps safe store

theorem afterXmit_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (cryptWork : PrefixM E Unit) (h_cryptWork : PrefixPreserves I S cryptWork)
    (sendWork : PrefixM E Unit) (h_sendWork : PrefixPreserves I S sendWork)
    : PrefixPreserves I S (afterXmitWith old cryptWork sendWork) := by
  unfold afterXmitWith
  repeat' first
    | (scheduler_preserve_at cryptWork; exact h_cryptWork)
    | (scheduler_preserve_at sendWork; exact h_sendWork)
    | deferred_atom_steps atoms
    | deferred_raw_steps safe store

theorem timers_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (cryptWork : PrefixM E Unit) (h_cryptWork : PrefixPreserves I S cryptWork)
    (j : UInt64)
    : PrefixPreserves I S (timersWith old cryptWork j) := by
  unfold timersWith
  repeat' first
    | (scheduler_preserve_at cryptWork; exact h_cryptWork)
    | deferred_atom_steps atoms
    | deferred_raw_steps safe store

theorem placeholder_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (cryptWork : PrefixM E Unit) (h_cryptWork : PrefixPreserves I S cryptWork)
    (sendWork : PrefixM E Unit) (h_sendWork : PrefixPreserves I S sendWork)
    (j : UInt64)
    : PrefixPreserves I S (placeholderWith old cryptWork sendWork j) := by
  unfold placeholderWith
  repeat' first
    | (scheduler_preserve_at cryptWork; exact h_cryptWork)
    | (scheduler_preserve_at sendWork; exact h_sendWork)
    | deferred_atom_steps atoms
    | deferred_raw_steps safe store

theorem idle_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (timers : UInt64 → PrefixM E Bool) (h_timers : ∀ j, PrefixPreserves I S (timers j))
    (placeholder : UInt64 → PrefixM E Unit) (h_placeholder : ∀ j, PrefixPreserves I S (placeholder j))
    : PrefixPreserves I S (idleWith old timers placeholder) := by
  unfold idleWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | (scheduler_preserve_at timers; exact h_timers _)
    | (scheduler_preserve_at placeholder; exact h_placeholder _)
    | deferred_atom_steps atoms
    | deferred_raw_steps safe store

theorem afterAdvance_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (timers : UInt64 → PrefixM E Bool) (h_timers : ∀ j, PrefixPreserves I S (timers j))
    (placeholder : UInt64 → PrefixM E Unit) (h_placeholder : ∀ j, PrefixPreserves I S (placeholder j))
    : PrefixPreserves I S (afterAdvanceWith old timers placeholder) := by
  unfold afterAdvanceWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | (scheduler_preserve_at timers; exact h_timers _)
    | (scheduler_preserve_at placeholder; exact h_placeholder _)
    | deferred_atom_steps atoms
    | deferred_raw_steps safe store

theorem deferred_preserves
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (cryptWork sendWork afterXmitWork : PrefixM E Unit)
    (timers : UInt64 → PrefixM E Bool) (placeholder : UInt64 → PrefixM E Unit)
    (idle afterAdvanceWork : PrefixM E Unit)
    (hc : PrefixPreserves I S cryptWork) (hs : PrefixPreserves I S sendWork)
    (hx : PrefixPreserves I S afterXmitWork)
    (ht : ∀ j, PrefixPreserves I S (timers j)) (hp : ∀ j, PrefixPreserves I S (placeholder j))
    (hi : PrefixPreserves I S idle) (ha : PrefixPreserves I S afterAdvanceWork)
    (call : EnvDeferredCall) :
    PrefixPreserves I S (deferredWith old cryptWork sendWork afterXmitWork timers placeholder idle afterAdvanceWork call) := by
  cases call with
  | drained what queues => exact atoms.drained what queues
  | idleDevice => exact atoms.idleDevice
  | noCrypt => exact atoms.noCrypt
  | crypt => exact hc
  | sendOne => exact atoms.sendOne
  | clearOne => exact atoms.clearOne
  | sendAll => exact hs
  | afterXmit => exact hx
  | timerWorker timer => exact atoms.timerWorker timer
  | timers j => exact ht j
  | placeholder j => exact hp j
  | idle => exact hi
  | advance ticks => exact atoms.advance ticks
  | afterAdvance => exact ha

/-- The concrete old RX embedding proves every atomic premise from its exact
source and routing frame. Newly reached TX receipts still belong to the
explicit committed callbacks, never to this old embedding. -/
theorem transmit_atoms (initial : FlatTable × FlatTable) :
    AtomContracts (TransmitJoint.Inv initial) (TransmitJoint.Safe initial)
      (fun {_} g => TransmitJoint.oldRx g) :=
  AtomContracts.of_routing _ (fun g a _ erased routing =>
    TransmitJoint.oldRx_preserves initial g a erased routing)

end Leanux.Proofs.WG.Queues.RxHistory.DeferredSource
