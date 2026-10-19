import Leanux.Proofs.WG.RetirementSecurity.HolderDeviceConflict
import Leanux.Proofs.WG.RetirementSecurity.MaterialFrames

/-! The actual static-identity finishing path retains the exact key account.
Expiry changes validity without paying credit; staged sends retain their own
allocation and current-slot premises at the precise source call. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDevice
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open StackOwnership HolderKeepalive

theorem join {action : WG.M α} (keys : Preserves (ReceiveEntry.Ready temporary) action)
    (slots : Preserves CurrentSlots.Inv action) : Preserves (Ready temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp keys w a result v b ⟨before.1,before.2.1⟩ run
  exact ⟨kept.1,kept.2,(hoare_iff_run_ambient _ _ _).mp slots w a result v b before.2.2 run⟩

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Ready temporary) action :=
  join (ReceiveEntry.store same) (CurrentSlots.fields_preserves (project:=id)
    (same.of_factor (fun s : WGStoreView=>CurrentSlots.fields {dev:=s.dev}) _ (fun _=>rfl)))

theorem configuration_points {action : WG.M α} (same : SameConfiguration action) :
    SameView ownershipPointView action := by
  apply same.of_factor (fun s : WGOwnedView=>ownershipPointView {dev:=s.dev})
  intro w
  unfold ownershipPointView ownershipAt keyReferenceView keyAt peerAt packetKeyWords
  cases hd:w.dev <;> simp [configurationView,configurationDevice,wgOwnedView,wgStoreView,hd]

theorem configuration {action : WG.M α} (same : SameConfiguration action) : Preserves (Ready temporary) action :=
  join (HolderResponse.points (erasesStatePrefix_lift _)
    (configurationLift_preserves_native allocationAmbient allocationConfigurationStable _
      (same.factor WGOwnedView.toWGStoreView)) (configuration_points same))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.configuration) same)

theorem socket_points {action : WG.M α} (same : SameSocket action) :
    SameView ownershipPointView action := by
  apply same.of_factor (fun s : WGOwnedView=>ownershipPointView {dev:=s.dev})
  intro w
  unfold ownershipPointView ownershipAt keyReferenceView keyAt peerAt packetKeyWords
  cases hd:w.dev <;> simp [socketView,socketDevice,wgOwnedView,wgStoreView,hd]

theorem clear_endpoint_points (pid : PeerId) : SameView ownershipPointView (clearPeerEndpointSrc pid) := by
  intro initial
  change Preserves (fun w=>ownershipPointView w=initial) _
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp (config:={zeta:=false}) only [getAmbient,hiddenJiffies]
  repeat' ownership_source_step initial

theorem port_points (port : Nat) : SameView ownershipPointView (setPort port) := by
  intro initial
  change Preserves (fun w=>ownershipPointView w=initial) _
  unfold setPort
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact (clear_endpoint_points _).wp (·=initial))
    | (rx_retention_head socketInit; exact (socket_points (socketInit_sameSocket _)).wp (·=initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec ownershipPointView (·=initial)
       intro x b
       change Preserves (fun w=>ownershipPointView w=initial) _)
    | ownership_source_step initial

theorem port (port : Nat) : Preserves (Ready temporary) (setPort port) :=
  join (HolderResponse.points (ConfigurationCall.erases (.port port))
    (ConfigurationCall.allocation (.port port)) (port_points port)) (CurrentSlots.Device.port port)

theorem precompute (pid : PeerId) : Preserves (Ready temporary) (precomputeStaticStatic pid) :=
  join (HolderResponse.points (precomputeStaticStaticMixed_erases pid)
    (precomputeStaticStaticMixed_allocation pid) (HolderPeerCreation.precompute_points pid))
    (CurrentSlots.fields_preserves (project:=id) (CurrentSlots.precomputeStaticStatic_fields pid))

theorem points_keys {action : WG.M α} (same : SameView ownershipPointView action) :
    Preserves (HolderAccount temporary) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.points ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem expire_keys (pid : PeerId) : Preserves (HolderAccount temporary) (expireCurrentPeerKeypairs pid) := by
  have invalidate (id : KeypairId) : Preserves (HolderAccount temporary)
      (do let k ← getKeypair id; setKeypair id {k with sending:={k.sending with isValid:=false}}) :=
    key_update_holders id (fun k=>{k with sending:={k.sending with isValid:=false}}) (fun _=>rfl) (fun _=>rfl) temporary
  unfold expireCurrentPeerKeypairs requireNotPending
  apply preserves_bind (preserves_pure ())
  intro _
  apply preserves_bind (points_keys (ClearedSlots.handshake_clear_points pid))
  intro _
  apply preserves_bind (points_keys (HolderPeerCreation.reset_points pid))
  intro _
  apply preserves_bind (getPeer_preserves pid _)
  intro p
  have one (decision : Decision) (kp : Option KeypairId) : Preserves (HolderAccount temporary)
      (do if ← branch decision kp.isSome then
            let some id := kp | invariant "unreachable"
            let k ← getKeypair id
            setKeypair id {k with sending:={k.sending with isValid:=false}}) := by
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch decision kp.isSome) _)
    intro selected
    cases selected with
    | false=>exact preserves_pure ()
    | true=>cases kp with
      | none=>exact hoare_liftAmbient (AmbientM.invariant "unreachable") _
      | some id=>exact invalidate id
  have current := one .expireCurrentKeypair p.keypairCurrent
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .expireNextKeypair p.keypairNext.isSome) _)
  intro selected
  cases selected with
  | false=>exact current
  | true=>cases p.keypairNext with
    | none=>exact preserves_bind (hoare_liftAmbient (AmbientM.invariant "unreachable") _) (fun _=>current)
    | some id=>exact preserves_bind (invalidate id) (fun _=>current)

theorem expire (pid : PeerId) : Preserves (Ready temporary) (expireCurrentPeerKeypairs pid) :=
  join (HolderResponse.join (KeyMaintenanceCall.erases (.expire pid))
    (KeyMaintenanceCall.allocation (.expire pid)) (expire_keys pid))
    (CurrentSlots.expireCurrentPeerKeypairs_preserves pid)

macro "holder_device_ready_step" : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire _)
  | (rx_retention_head sendStagedPackets; exact HolderKeepalive.staged _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Ready _)
     intro x b
     change Preserves (Ready _) _)
  | rx_retention_step)

theorem finish (key : Key) : Preserves (Ready temporary)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config:={zeta:=false}) only [branch]
  repeat' holder_device_ready_step

end Leanux.Proofs.WG.RetirementSecurity.HolderDevice
