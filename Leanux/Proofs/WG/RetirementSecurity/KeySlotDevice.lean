import Leanux.Proofs.WG.RetirementSecurity.KeySlotTimers
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.Proofs.WG.Queues.DeviceStages

/-! Original device configuration retains live key publication through port,
static-key, peer-replacement and peer-command source branches. All actual
clears and creation calls retain their separate local contracts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Configuration

theorem socket_frame {action : WG.M α} (same : SameSocket action) : Preserves (InvExcept pending) action := by
  apply frame
  apply same.of_factor (fun s : WGOwnedView=>view {dev:=s.dev}) view
  intro w
  funext pid
  simp only [view,peerAt,socketView,socketDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (InvExcept pending) action := by
  apply frame
  apply same.of_factor (fun s : WGOwnedView=>view {dev:=s.dev}) view
  intro w
  funext pid
  simp only [view,peerAt,configurationView,configurationDevice,wgOwnedView,wgStoreView,
    Option.bind_map,Function.comp_def]

theorem set_port (port : Nat) : Preserves (InvExcept pending) (setPort port) := by
  unfold setPort
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_frame (socketInit_sameSocket _))
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | key_slot_rx_step

theorem device_peers (attrs : DeviceAttrs) : Preserves (InvExcept pending) (devicePeersSource attrs) := by
  unfold devicePeersSource
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact config_command _)
    | key_slot_rx_step

macro "key_slot_device_step" : tactic => `(tactic| first
  | (rx_retention_head pubkeyLookup; exact pubkey _)
  | (rx_retention_head devicePeersSource; exact device_peers _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (InvExcept _))
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire _)
  | (rx_retention_head sendStagedPackets; exact staged _)
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head setPort; exact set_port _)
  | (rx_retention_head peerRemoveAll; exact all_peers)
  | (rx_retention_head peerRemove; exact remove_peer _)
  | key_slot_rx_step)

theorem device_key_finish (key : Key) : Preserves (InvExcept pending)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config := {zeta:=false}) only [branch]
  repeat' key_slot_device_step

theorem device_key_conflict (key : Key) : Preserves (InvExcept pending)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict
  simp (config := {zeta:=false}) only [branch]
  repeat' key_slot_device_step

theorem device_key_changed (key : Key) : Preserves (InvExcept pending)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp (InvExcept pending))
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) _)
  intro generated
  cases generated with
  | false=>exact device_key_finish key
  | true=>
    cases pub with
    | none=>exact preserves_bind (hoare_liftAmbient
        (AmbientM.invariant "a generated public key without a write") _) (fun _=>device_key_finish key)
    | some pub=>exact preserves_bind (device_key_conflict pub) (fun _=>device_key_finish key)

theorem device_key (attrs : DeviceAttrs) : Preserves (InvExcept pending) (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' key_slot_device_step
  all_goals exact device_key_changed _

theorem device_update (attrs : DeviceAttrs) (flags : UInt32) :
    Preserves (InvExcept pending) (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact device_key _)
    | key_slot_device_step

theorem set_device (attrs : DeviceAttrs) : Preserves (InvExcept pending) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (InvExcept pending))
    | (rx_retention_head deviceUpdateSource; exact device_update _ _)
    | key_slot_device_step

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
