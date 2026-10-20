import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigConcreteSource

/-! Quiet configuration atoms retain both packet projection and allocation.
Creation instead uses the initialized allocation invariant to derive freshness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity CausalJournal Lifetimes RetirementSecurity Queues

theorem NativeKind.checked (token : NativeKind) : CompleteProduct.Checked token.action := by
  cases token with
  | quiet action frame allocated=>
      exact CompleteProduct.state (CompleteConfigurationReady.passive CompleteProduct.Safe
        CompleteProduct.account_safe action frame allocated)
  | create key psk=>
      exact CompleteProduct.state
        (CompleteAllocated.create CompleteProduct.Safe CompleteProduct.account_safe key psk)

macro "config_native_frames" : tactic => `(tactic| (
  apply quietShape
  · first
    | (snapshot_head setAllowedip; exact RoutingFrames.set _ _)
    | (snapshot_head removeByPeer; exact RoutingFrames.remove _)
    | entry_device_frame
  · first
    | (rx_retention_head setAllowedip; exact AllocatedFrames.configured (.allowedIp _ _))
    | (rx_retention_head setPeerEndpoint; exact AllocatedFrames.observed (setPeerEndpointPrefix_erases _ _)
        (AmbientContracts.drop (setPeerEndpointPrefix_spec allocationAmbient (fun _=>True) _ _)))
    | (rx_retention_head removeByPeer; exact AllocatedFrames.observed (removeByPeerPrefix_erases _)
        (removeByPeerPrefix_preserves allocationAmbient allocationConfigurationPeer.removal.allowedIps.nodes _))
    | entry_device_allocation))

theorem psk_checked (pid : PeerId) (psk : Option Key) :
    CompleteProduct.Checked (liftWGObserver (pskUpdate pid psk)) := by
  apply CompleteProduct.state
  simpa only [pskUpdate,Queued.lift_bind] using
    CompleteConfigurationReady.passive CompleteProduct.Safe CompleteProduct.account_safe
      (getPeer pid >>= fun p=>setPeer pid {p with presharedKey:=psk.getD []})
      (Queued.update pid _ (fun _=>⟨rfl,rfl,rfl⟩))
      (AllocatedFrames.update pid _ (fun _=>rfl))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
