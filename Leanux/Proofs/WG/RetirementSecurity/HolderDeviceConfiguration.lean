import Leanux.Proofs.WG.RetirementSecurity.HolderDeviceFrames

/-! The full native device command preserves joint key/peer funding. Identity
conflict removal, bulk removal and each peer command use their concrete
reference-payment proofs; ordinary device fields are explicit projections. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits Configuration

theorem join {action : WG.M α}
    (keys : Preserves (HolderKeepalive.Ready temporary) action)
    (peers : Preserves (DeviceBoundary.Entry carriers loans) action)
    (physical : SameView RxRing.nativeCell action)
    (live : Preserves KeySlotLiveness.Inv action) : Preserves (Entry temporary carriers loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp keys w a result v b before.1 run
  exact ⟨kept,⟨(hoare_iff_run_ambient _ _ _).mp peers w a result v b before.2.1.1 run,
    HolderStopPhysical.optional_cell before.2.1.2.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp physical w a result v b run),kept.2.2⟩,
    (hoare_iff_run_ambient _ _ _).mp live w a result v b before.2.2 run⟩

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Entry temporary carriers loans) action :=
  join (HolderDevice.store same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.store) same)
    (same.of_factor (fun s : WGStoreView=>s.dev.map fun d=>(d.ifindex,d.decryptQueue)) _ (fun _=>rfl))
    (KeySlotLiveness.store same)

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Entry temporary carriers loans) action :=
  join (HolderDevice.configuration same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.configuration) same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DevicePhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.DevicePhysical.configuration_cell) same)
    (KeySlotLiveness.configuration_frame same)

theorem port (number : Nat) : Preserves (Entry temporary carriers loans) (setPort number) :=
  join (HolderDevice.port number) (DeviceStages.port number) (DevicePhysical.port_cell number) (KeySlotLiveness.set_port number)

theorem clear_endpoint (pid : PeerId) : Preserves (Entry temporary carriers loans) (clearPeerEndpointSrc pid) :=
  join (HolderDevice.join
      (HolderResponse.points (clearPeerEndpointSrcPrefix_erases pid)
        (AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec allocationAmbient (fun _=>True) pid))
        (HolderDevice.clear_endpoint_points pid)) (CurrentSlots.Device.clearEndpoint pid))
    (DeviceStages.clearEndpoint pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DevicePhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.DevicePhysical.clearEndpoint_cell) pid)
    (KeySlotLiveness.clear_endpoint pid)

theorem finish (key : Key) : Preserves (Entry temporary carriers loans)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) :=
  join (HolderDevice.finish key)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish_keeps) key)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DevicePhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.DevicePhysical.keyFinish_cell) key)
    (KeySlotLiveness.device_key_finish key)

theorem changed (key : Key) : Preserves (Entry temporary carriers loans)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp (Entry temporary carriers loans))
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) _)
  intro generated
  cases generated with
  | false=>exact finish key
  | true=>
    cases pub with
    | none=>
      exact preserves_bind (hoare_liftAmbient (AmbientM.invariant "a generated public key without a write") _)
        (fun _=>finish key)
    | some pub=>exact preserves_bind (conflict_entry pub) (fun _=>finish key)

macro "holder_boundary_device_step" : tactic => `(tactic| first
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head devicePeersSource; exact peer_list _)
  | (rx_retention_head setPort; exact port _)
  | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
  | (rx_retention_head peerRemoveAll; exact remove_all)
  | (rx_retention_head modifyDev; first
      | exact configuration_frame generation_sameConfiguration
      | exact configuration_frame (fwmark_sameConfiguration _))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Entry _ _ _)
     intro x b
     change Preserves (Entry _ _ _) _)
  | rx_retention_step)

theorem key (attrs : DeviceAttrs) : Preserves (Entry temporary carriers loans) (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' holder_boundary_device_step
  all_goals exact changed _

theorem update (attrs : DeviceAttrs) (flags : UInt32) :
    Preserves (Entry temporary carriers loans) (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact key _)
    | holder_boundary_device_step

theorem device (attrs : DeviceAttrs) : Preserves (Entry temporary carriers loans) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Entry _ _ _))
    | (rx_retention_head deviceUpdateSource; exact update _ _)
    | holder_boundary_device_step

end Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
