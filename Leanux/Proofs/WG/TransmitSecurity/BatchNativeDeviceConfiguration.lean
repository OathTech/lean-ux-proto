import Leanux.Proofs.WG.TransmitSecurity.BatchNativePeerConfiguration

/-! Full device configuration transports batch alignment through peer
replacement, routing changes, key expiry and guarded staged sends. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Configuration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits Native Leanux.Proofs.WG.Configuration

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Coherent locals active) action := by
  apply coherent_join (OccurrenceConfiguration.configuration_frame same)
  apply contents_wire
  · exact same.of_factor (fun s : WGOwnedView => txQueueContents {dev := s.dev}) _
      (fun w => by funext pid; simp only [configurationView,configurationDevice,txQueueContents,handoffTxView,
        wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def])
  · exact same.of_factor (fun s : WGOwnedView => txCryptWire {dev := s.dev}) _
      (fun w => by simp only [configurationView,configurationDevice,txCryptWire,TxRing.nativeCell,
        TxDisposition.txPackets,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

theorem expire_keys (pid : PeerId) : Preserves (Coherent locals active) (expireCurrentPeerKeypairs pid) :=
  coherent_join (OccurrenceConfiguration.expire_keys pid) (expire pid)

theorem device_peers (attrs : DeviceAttrs) : Preserves (Coherent locals active) (devicePeersSource attrs) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact set_peer _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | batch_config_step

macro "batch_device_step " locals:term:max active:term:max : tactic => `(tactic| first
  | (rx_retention_head pubkeyLookup; exact pubkey _)
  | (rx_retention_head devicePeersSource; exact device_peers _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Coherent $locals $active))
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire_keys _)
  | (rx_retention_head sendStagedPackets; exact send_coherent _)
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head setPort; exact set_port _)
  | (rx_retention_head peerRemoveAll; exact Removal.remove_all)
  | (rx_retention_head peerRemove; exact Removal.remove _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Coherent $locals $active)
     intro x b
     change Preserves (Coherent $locals $active) _)
  | batch_config_step)

private theorem key_finish (key : Key) : Preserves (Coherent locals active)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' batch_device_step locals active

private theorem key_conflict (key : Key) : Preserves (Coherent locals active)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict
  simp (config := {zeta := false}) only [branch]
  repeat' batch_device_step locals active

private theorem key_changed (key : Key) : Preserves (Coherent locals active)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp (Coherent locals active))
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) (Coherent locals active))
  intro generated
  cases generated with
  | false => exact key_finish key
  | true =>
    cases pub with
    | none =>
      exact preserves_bind (hoare_liftAmbient
        (AmbientM.invariant "a generated public key without a write") (Coherent locals active))
        (fun _ => key_finish key)
    | some pub =>
      exact preserves_bind (key_conflict pub) (fun _ => key_finish key)

theorem device_key (attrs : DeviceAttrs) : Preserves (Coherent locals active) (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' batch_device_step locals active
  all_goals exact key_changed _

theorem device_update (attrs : DeviceAttrs) (flags : UInt32) : Preserves (Coherent locals active) (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact device_key _)
    | batch_device_step locals active

theorem set_device (attrs : DeviceAttrs) : Preserves (Coherent locals active) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Coherent locals active))
    | (rx_retention_head deviceUpdateSource; exact device_update _ _)
    | batch_device_step locals active


end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Configuration
