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
  | metadata action source allocated=>
      exact CompleteProduct.state (CompleteConfigurationReady.passive CompleteProduct.Safe
        CompleteProduct.account_safe action source.frame allocated)
  | lookup action source allocated=>
      exact CompleteProduct.state (CompleteConfigurationReady.passive CompleteProduct.Safe
        CompleteProduct.account_safe action source.frame allocated)
  | routing action source allocated=>
      exact CompleteProduct.state (CompleteConfigurationReady.passive CompleteProduct.Safe
        CompleteProduct.account_safe action source.frame allocated)
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

macro "config_metadata_shape" : tactic => `(tactic| first
  | (metadata_source_head precomputeStaticStatic; exact PeerMetadata.precomputeShape _)
  | (metadata_source_head expireCurrentPeerKeypairs; exact PeerMetadata.expireShape _)
  | (metadata_source_head clearPeerEndpointSrc; exact PeerMetadata.clearEndpointShape _)
  | (metadata_source_head setPeerEndpoint; exact PeerMetadata.setEndpointShape _ _)
  | (metadata_source_head setPort; exact PeerMetadata.setPortShape _)
  | (metadata_source_head lookupInterface; exact PeerMetadata.interfaceShape _)
  | (metadata_source_head setStaticIdentityPrivateKey; exact PeerMetadata.staticIdentityShape _)
  | (metadata_source_head cookiePrecomputeDeviceKeys; exact PeerMetadata.deviceCookieShape)
  | (metadata_source_head peerGet; exact PeerMetadata.peerGetShape _)
  | metadata_source_step)

open Lean Meta Elab Tactic in
elab "config_native_head " expected:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Shape do throwError "not a configuration source"
  let action := target.getAppArgs.back!.consumeMData
  unless action.isAppOf ``liftWGObserver do throwError "not a WG observer"
  let body := action.getAppArgs.back!.consumeMData
  unless body.isAppOf ``liftWGPrefix do throwError "not a native lift"
  let native := body.getAppArgs.back!.consumeMData.headBeta
  let name ← realizeGlobalConstNoOverloadWithInfo expected
  unless native.getAppFn.constName? == some name do throwError "different native source head"

noncomputable def publicLookupShape (key : Key) : Shape (liftWGObserver (liftWGPrefix (pubkeyLookup key))) :=
  lookupShape _ (Lookup.pubkeyShape key) (AllocatedFrames.public_lookup key)

macro "config_native_source" : tactic => `(tactic| first
  | (config_native_head setAllowedip; refine routingShape _ (Routing.setShape _ _) ?_;
      exact AllocatedFrames.configured (.allowedIp _ _))
  | (config_native_head removeByPeer; refine routingShape _ (Routing.removeShape _) ?_;
      exact AllocatedFrames.observed (removeByPeerPrefix_erases _)
        (removeByPeerPrefix_preserves allocationAmbient allocationConfigurationPeer.removal.allowedIps.nodes _))
  | (config_native_head Leanux.WG.pubkeyLookup; exact publicLookupShape _)
  | (apply metadataShape
     · repeat' config_metadata_shape
     · first
       | (rx_retention_head setPeerEndpoint; exact AllocatedFrames.observed (setPeerEndpointPrefix_erases _ _)
           (AmbientContracts.drop (setPeerEndpointPrefix_spec allocationAmbient (fun _=>True) _ _)))
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
