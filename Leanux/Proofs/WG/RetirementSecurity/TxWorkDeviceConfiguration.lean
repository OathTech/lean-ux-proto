import Leanux.Proofs.WG.RetirementSecurity.TxWorkPeerConfiguration

/-! Full native device configuration preserves TX service through peer
replacement, routing changes, key expiry and actual guarded staged sends.
The local source contract retains its incoming carrier explicitly. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork.Configuration
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Leanux.Proofs.WG.Configuration

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Serving locals crypt tx) action := by
  apply serving_join
  · apply passive_contents
    · exact same.of_factor (fun s : WGOwnedView=>txCryptWire {dev:=s.dev}) _
        (fun w=>by simp only [configurationView,configurationDevice,txCryptWire,TxRing.nativeCell,
          TxDisposition.txPackets,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])
    · exact same.of_factor (fun s : WGOwnedView=>txQueueContents {dev:=s.dev}) _
        (fun w=>by funext pid; simp only [configurationView,configurationDevice,txQueueContents,handoffTxView,
          wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def])
    · exact same.of_factor (fun s : WGOwnedView=>queued {dev:=s.dev}) _
        (fun w=>by simp only [configurationView,configurationDevice,queued,wgOwnedView,wgStoreView,
          Option.map_map,Function.comp_def])
  · exact TxCovered.Configuration.configuration_frame same

theorem expire_keys (pid : PeerId) : Preserves (Serving locals crypt tx) (expireCurrentPeerKeypairs pid) :=
  serving_join (passive (OccurrenceKeys.expire_wire pid) (OccurrenceKeys.expire_queues pid) (expire_work pid))
    (TxCovered.Configuration.expire_keys pid)

theorem device_peers (attrs : DeviceAttrs) : Preserves (Serving locals crypt tx) (devicePeersSource attrs) := by
  unfold devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact set_peer _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Serving locals crypt tx)
       intro x b
       change Preserves (Serving locals crypt tx) _)
    | serving_config_step

macro "serving_device_step " locals:term:max crypt:term:max tx:term:max : tactic => `(tactic| first
  | (rx_retention_head pubkeyLookup; exact serving_pubkey _)
  | (rx_retention_head devicePeersSource; exact device_peers _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Serving $locals $crypt $tx))
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact serving_precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire_keys _)
  | (rx_retention_head sendStagedPackets; exact serving_staged _)
  | (rx_retention_head clearPeerEndpointSrc; exact serving_clear_endpoint _)
  | (rx_retention_head setPort; exact serving_set_port _)
  | (rx_retention_head peerRemoveAll; exact serving_remove_all)
  | (rx_retention_head peerRemove; exact serving_remove _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Serving $locals $crypt $tx)
     intro x b
     change Preserves (Serving $locals $crypt $tx) _)
  | serving_config_step)

private theorem key_finish (key : Key) : Preserves (Serving locals crypt tx)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' serving_device_step locals crypt tx

private theorem key_conflict (key : Key) : Preserves (Serving locals crypt tx)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyConflict
  simp (config := {zeta := false}) only [branch]
  repeat' serving_device_step locals crypt tx

private theorem key_changed (key : Key) : Preserves (Serving locals crypt tx)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp (Serving locals crypt tx))
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) (Serving locals crypt tx))
  intro generated
  cases generated with
  | false => exact key_finish key
  | true =>
    cases pub with
    | none =>
      exact preserves_bind (hoare_liftAmbient
        (AmbientM.invariant "a generated public key without a write") (Serving locals crypt tx))
        (fun _ => key_finish key)
    | some pub =>
      exact preserves_bind (key_conflict pub) (fun _ => key_finish key)

theorem device_key (attrs : DeviceAttrs) : Preserves (Serving locals crypt tx) (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' serving_device_step locals crypt tx
  all_goals exact key_changed _

theorem device_update (attrs : DeviceAttrs) (flags : UInt32) : Preserves (Serving locals crypt tx) (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact device_key _)
    | serving_device_step locals crypt tx

theorem set_device (attrs : DeviceAttrs) : Preserves (Serving locals crypt tx) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Serving locals crypt tx))
    | (rx_retention_head deviceUpdateSource; exact device_update _ _)
    | serving_device_step locals crypt tx


end Leanux.Proofs.WG.RetirementSecurity.TxWork.Configuration
