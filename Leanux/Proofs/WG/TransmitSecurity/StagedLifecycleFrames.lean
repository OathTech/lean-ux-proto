import Leanux.Proofs.WG.TransmitSecurity.StagedRemovalFrames
import Leanux.Proofs.Framing.WGDeviceLifecycle
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeLifecycleFrames

/-! Lifecycle frames retain staged provenance for surviving queues. Destroyed
devices have no resident obligation; a newly created device has no peer queues. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem pre_exit : Preserves (Inv h) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn; apply list_view_spec id (Inv h); intro x b; change Preserves (Inv h) _)
    | staged_configuration_native

theorem absent (w : WGWorld) (empty : w.dev = none) : Inv h w := by
  intro generation atEpoch
  simp only [Packets.epoch,empty,Option.map_none] at atEpoch
  cases atEpoch

theorem limiter : Preserves (Inv h) ratelimiterUninit := by
  apply frame
  · exact ratelimiterUninit_sameRatelimiter.of_factor
      (fun s : WGStoreView => s.dev.map Device.ifindex) Packets.epoch (fun _ => rfl)
  · exact Staged.of_view _ (ratelimiterUninit_sameRatelimiter.of_factor
      (fun s : WGStoreView => stagedAt {dev := s.dev}) stagedAt (fun _ => rfl))

theorem destruct_finish : Preserves (Inv h) HandshakeSecurity.Exchange.destructFinishSource := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b _ run
  cases value
  have gone := (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish_none)
    w v a b run
  apply absent
  simpa only [AllowedIps.routingView,Option.map_eq_none_iff] using gone

theorem device_create : Preserves (Inv h) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply before.retains
    · have fields := congrArg (fun s : WGStoreView => s.dev.map (·.ifindex)) same
      simpa only [Packets.epoch,linkView,linkStore,wgStoreView,linkDevice,Option.map_map,Function.comp_def] using fields
    · intro pid cell found
      have fields := congrArg (fun s : WGStoreView =>
        (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.staged)) same
      have queues : stagedAt v pid = stagedAt w pid := by
        simpa only [stagedAt,linkView,linkStore,wgStoreView,linkDevice,Option.bind_map,Function.comp_def] using fields
      exact queues ▸ found
  · intro _ _ pid stamp packets cell
    obtain ⟨d,hd,stored⟩ := Option.bind_eq_some_iff.mp (Option.map_eq_some_iff.mp cell).choose_spec.1
    have fields := congrArg (fun s : WGStoreView => s.dev.map (·.peers)) fresh
    have empty : d.peers = {} := by
      simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
        Option.map_some,Option.some.injEq] using fields
    simp [empty] at stored

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
