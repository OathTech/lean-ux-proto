import Leanux.Proofs.WG.Queues.SlotConfiguration
import Leanux.Proofs.WG.Queues.DeviceStages

/-! The unchanged three-slot invariant through the complete original device
configuration command, including conflict deletion and normal errno results. -/
namespace Leanux.Proofs.WG.CurrentSlots.Device
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Leanux.Proofs.WG.Configuration

private theorem configuration {action : WG.M α} (same : SameConfiguration action) : Preserves Inv action := by
  apply fields_preserves (project := id)
  apply same.of_factor (fun s : WGOwnedView => fields {dev:=s.dev})
  intro w
  unfold fields RxCredits.keyWords
  cases hd:w.dev <;> simp [configurationView,configurationDevice,wgOwnedView,wgStoreView,hd]

private theorem socket {action : WG.M α} (same : SameSocket action) : Preserves Inv action := by
  apply fields_preserves (project := id)
  apply same.of_factor (fun s : WGOwnedView => fields {dev:=s.dev})
  intro w
  unfold fields RxCredits.keyWords
  cases hd:w.dev <;> simp [socketView,socketDevice,wgOwnedView,wgStoreView,hd]

theorem clearEndpoint (pid : PeerId) : Preserves Inv (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' slot_remove_step

theorem port (port : Nat) : Preserves Inv (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint _)
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _))
    | slot_remove_step

theorem peers (attrs : DeviceAttrs) : Preserves Inv (devicePeersSource attrs) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact Configuration.command _)
    | slot_remove_step

macro "slot_device_step" : tactic => `(tactic| first
  | (rx_retention_head pubkeyLookup; exact Configuration.pubkey_preserves _)
  | (rx_retention_head devicePeersSource; exact peers _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp Inv)
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact fields_preserves (project := id) (precomputeStaticStatic_fields _))
  | (rx_retention_head expireCurrentPeerKeypairs; exact expireCurrentPeerKeypairs_preserves _)
  | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _)
  | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint _)
  | (rx_retention_head setPort; exact port _)
  | (rx_retention_head peerRemoveAll; exact Removal.removeAll)
  | (rx_retention_head peerRemove; exact Removal.remove _)
  | slot_remove_step)

private theorem keyFinish_keeps (key : Key) : Preserves Inv
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' slot_device_step

private theorem keyConflict_keeps (key : Key) : Preserves Inv
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict
  simp (config := {zeta := false}) only [branch]
  repeat' slot_device_step

private theorem keyChanged_keeps (key : Key) : Preserves Inv
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp Inv)
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) Inv)
  intro generated
  cases generated with
  | false => exact keyFinish_keeps key
  | true =>
    cases pub with
    | none =>
      exact preserves_bind (hoare_liftAmbient
        (AmbientM.invariant "a generated public key without a write") Inv)
        (fun _ => keyFinish_keeps key)
    | some pub =>
      exact preserves_bind (keyConflict_keeps pub) (fun _ => keyFinish_keeps key)

theorem key (attrs : DeviceAttrs) : Preserves Inv (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' slot_device_step
  all_goals exact keyChanged_keeps _

theorem update (attrs : DeviceAttrs) (flags : UInt32) : Preserves Inv (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact key _)
    | slot_device_step

/-- Every normal success or errno result of the original command preserves
all three nullable key slots. No funding or configured-history premise is used. -/
theorem device (attrs : DeviceAttrs) : Preserves Inv (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp Inv)
    | (rx_retention_head deviceUpdateSource; exact update _ _)
    | slot_device_step

end Leanux.Proofs.WG.CurrentSlots.Device
