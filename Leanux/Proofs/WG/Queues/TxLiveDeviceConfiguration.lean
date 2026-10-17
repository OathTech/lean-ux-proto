import Leanux.Proofs.WG.Queues.TxLiveDevice
import Leanux.Proofs.WG.Queues.TxLivePeerConfiguration
import Leanux.Proofs.WG.Queues.DeviceStages

/-! Full native device configuration retains the TX live bound, including
conflict removal, staged sends, peer creation and all normal errno results. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

private theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves Ready action :=
  fields_ready (same.of_factor
    (fun k : WGOwnedView => k.dev.map fun d => (d.nextSkb,d.encryptQueue))
    _ (fun w => by simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
      Option.map_map,Function.comp_def]))

theorem set_port (port : Nat) : Preserves Ready (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | (rx_retention_head socketInit; exact socket_frame (socketInit_sameSocket _))
    | live_socket_step

theorem device_peers (attrs : DeviceAttrs) : Preserves Ready (devicePeersSource attrs) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact set_peer _)
    | live_socket_step

macro "live_device_step" : tactic => `(tactic| first
  | (rx_retention_head pubkeyLookup; exact pubkey_lookup _)
  | (rx_retention_head devicePeersSource; exact device_peers _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp Ready)
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire_keys _)
  | (rx_retention_head sendStagedPackets; exact send _)
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head setPort; exact set_port _)
  | (rx_retention_head peerRemoveAll; exact remove_all)
  | (rx_retention_head peerRemove; exact remove_peer _)
  | live_socket_step)

private theorem key_finish (key : Key) : Preserves Ready
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' live_device_step

private theorem key_conflict (key : Key) : Preserves Ready
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict
  simp (config := {zeta := false}) only [branch]
  repeat' live_device_step

private theorem key_changed (key : Key) : Preserves Ready
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp Ready)
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) Ready)
  intro generated
  cases generated with
  | false => exact key_finish key
  | true =>
    cases pub with
    | none =>
      exact preserves_bind (hoare_liftAmbient
        (AmbientM.invariant "a generated public key without a write") Ready)
        (fun _ => key_finish key)
    | some pub =>
      exact preserves_bind (key_conflict pub) (fun _ => key_finish key)

theorem device_key (attrs : DeviceAttrs) : Preserves Ready (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' live_device_step
  all_goals exact key_changed _

theorem device_update (attrs : DeviceAttrs) (flags : UInt32) : Preserves Ready (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact device_key _)
    | live_device_step

theorem set_device (attrs : DeviceAttrs) : Preserves Ready (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp Ready)
    | (rx_retention_head deviceUpdateSource; exact device_update _ _)
    | live_device_step

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
