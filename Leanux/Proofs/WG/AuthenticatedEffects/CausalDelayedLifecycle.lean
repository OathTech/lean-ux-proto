import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycleSourceFrames

/-! Native shutdown drains the same observed work callbacks. Deletion retires
all resident obligations; creation establishes an empty pending-timer and
send-work carrier from the actual native endpoint, without a fresh-state premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open Queues Configuration TransmitSecurity.Driver HandshakeSecurity.SendExchange TimerSlots
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem absent (h : List Event) (w : WGWorld) (empty : w.dev = none) : Inv h w := by
  simpa only [List.nil_append] using
    (DelayedEffects.Inv.empty_device Event.armed Event.queued w empty).append h

theorem limiter : StateSafe (liftWGPrefix ratelimiterUninit) := by
  apply state_framed
  · intro initial
    apply retained_exact
    exact ratelimiterUninit_sameRatelimiter.of_factor
      (fun s pid t => (s.dev.bind fun d => d.peers[pid]?).map
        (fun p => (p.internalId,p.timer t,p.wheel t))) TimerSlots.view (fun _ => rfl)
  · exact ratelimiterUninit_sameRatelimiter.of_factor
      (fun s => (s.dev.map Device.sendWorkQueue).getD []) QueuedOccurrences.queue (fun _ => rfl)

theorem purge_staged (pid : PeerId) : StateSafe (liftWGPrefix (purgeStagedPackets pid)) := by
  apply state_framed
  · intro initial
    unfold purgeStagedPackets
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold purgeStagedPackets
    repeat' send_work_frame_step initial

theorem destruct_finish : StateSafe (liftWGPrefix
    (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish)) := by
  apply state_native
  intro h
  index_unfold _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish
  simp only [unsupported,invariant]
  repeat' first
    | (rx_retention_head mayHaveSlept; exact native_contract _ (native_store _ mayHaveSlept_sameWGStore) h)
    | (rx_retention_head ratelimiterUninit; exact native_contract _ limiter h)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact absent h _ rfl)
    | (rx_retention_head retireDeviceUnits; exact native_contract _ (native_store _ retireDeviceUnits_sameWGStore) h)
    | (rx_retention_head getDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) h)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

macro "causal_delayed_lifecycle_step" : tactic => `(tactic| first
  | (causal_delayed_native_head requireNotPending; unfold requireNotPending; exact state_pure _)
  | (causal_delayed_native_head purgeStagedPackets; exact purge_staged _)
  | (causal_delayed_native_head handshakeClear; exact clear_handshake _)
  | (causal_delayed_native_head resetLastSentHandshake; exact reset_handshake _)
  | (causal_delayed_native_head socketReinit; exact socket_native _ (socketReinit_sameSocket _ _))
  | causal_delayed_removal_step)

theorem down : StateSafe (downObserved hooks) := by
  unfold downObserved
  rw [show hooks.stagedPurge = (fun pid => liftWGPrefix (purgeStagedPackets pid)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.down_neutral]
  unfold downWith stopWith timersStopWith
  repeat' first
    | (causal_delayed_head sendDrainObserved; exact sendDrain _)
    | causal_delayed_lifecycle_step

theorem destruct : StateSafe (destructObserved hooks) := by
  change StateSafe (Configuration.destructWith liftWGPrefix (removeAllObserved hooks) _)
  unfold Configuration.destructWith
  repeat' first
    | (causal_delayed_head removeAllObserved; exact removeAll)
    | causal_delayed_lifecycle_step
  exact destruct_finish

theorem device_create : StateSafe (liftWGPrefix wgCreate) := by
  apply state_native
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w)) w a value v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply hi.retained
    · have peers := congrArg (fun s : WGStoreView => s.dev.map Device.peers) same
      intro pid t token pending
      have actual : v.dev.map Device.peers = w.dev.map Device.peers := by
        simpa only [linkView,linkStore,linkDevice,wgStoreView,Option.map_map,Function.comp_def] using peers
      have obs := congrArg (fun s => (s.bind fun ps => ps[pid]?).map
        (fun p => (p.internalId,p.timer t,p.wheel t))) actual
      have exactSlots : TimerSlots.view v pid t = TimerSlots.view w pid t := by
        simpa only [TimerSlots.view,Option.bind_map,Function.comp_def] using obs
      exact exactSlots ▸ pending
    · have queue := congrArg (fun s : WGStoreView => (s.dev.map Device.sendWorkQueue).getD []) same
      simpa only [QueuedOccurrences.queue,linkView,linkStore,linkDevice,wgStoreView,
        Option.map_map,Function.comp_def] using queue
  · have peers := congrArg (fun s : WGStoreView => s.dev.map Device.peers) fresh
    have queue := congrArg (fun s : WGStoreView => (s.dev.map Device.sendWorkQueue).getD []) fresh
    refine ⟨?_,[],?_⟩
    · intro pid t stamp expires entry pending
      cases hd : v.dev with
      | none => simp [Pending,TimerSlots.view,hd] at pending
      | some d =>
        have empty : d.peers = {} := by
          simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
            hd,Option.map_some,Option.some.injEq] using peers
        simp [Pending,TimerSlots.view,hd,empty] at pending
    · have empty : QueuedOccurrences.queue v = [] := by
        simpa only [QueuedOccurrences.queue,linkView,linkStore,linkDevice,wgStoreView,
          registeredLink,setupLink,Option.map_some,Option.map_map,Function.comp_def,Option.getD_some] using queue
      simpa only [List.nil_append] using
        (QueuedOccurrences.Carrier.empty (record := Event.queued) v empty).append h

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
