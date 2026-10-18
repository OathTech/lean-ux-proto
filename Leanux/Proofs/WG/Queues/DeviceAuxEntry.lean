import Leanux.Proofs.WG.Queues.SlotDevice
import Leanux.Proofs.WG.Queues.HolderStopPhysical
import Leanux.Proofs.WG.Origins.CurrentDevice

/-! Native lifecycle entry components at the same actual normal endpoint.
Creation uses the original guarded endpoint; shutdown keeps its recorded Stops
and may delete peers while draining their charged work. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DeviceAuxEntry
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- Existing supplied funding, structural/configured identity, physical ring
alternative and nullable three-slot compatibility, without historical receipts. -/
def Entry (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  DeviceBoundary.Entry cs loans w ∧ HolderDeviceCreate.OptionalPhysical w ∧ CurrentSlots.Inv w

private theorem slots_link (w : WGWorld) :
    CurrentSlots.fields {dev:=(linkView w).dev}=CurrentSlots.fields w := by
  unfold CurrentSlots.fields RxCredits.keyWords
  simp only [linkView,linkStore,linkDevice,wgStoreView,
    Option.map_map,Option.map_bind,Option.bind_map,Function.comp_def]

private theorem base_link (w : WGWorld) :
    BaseCoherence.view {dev:=(linkView w).dev}=BaseCoherence.view w := by
  simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,
    linkView,linkStore,linkDevice,wgStoreView,Option.map_map,Function.comp_def]

private theorem configured_link (w : WGWorld) :
    (linkView w).dev.map ConfiguredIdentity.state=ConfiguredIdentity.view w := by
  simp only [linkView,linkStore,linkDevice,wgStoreView,ConfiguredIdentity.view,
    ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

theorem create_slots : Preserves CurrentSlots.Inv wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply CurrentSlots.fields_transport hi
    have fields := congrArg (fun s : WGStoreView => CurrentSlots.fields {dev:=s.dev}) same
    simpa only [slots_link] using fields
  · apply (CurrentSlots.inv_iff v).mpr
    intro d pid p kid hd hp _
    have peers := congrArg (fun s : WGStoreView => s.dev.map Device.peers) fresh
    simp only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,
      hd,Option.map_some,Option.some.injEq] at peers
    simp [peers] at hp

theorem create_base : Preserves BaseCoherence.Inv wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply BaseCoherence.transport hi
    have fields := congrArg (fun s : WGStoreView => BaseCoherence.view {dev:=s.dev}) same
    simpa only [base_link] using fields
  · have fields := congrArg (fun s : WGStoreView => BaseCoherence.view {dev:=s.dev}) fresh
    rw [base_link] at fields
    have empty : BaseCoherence.view v=([],[]) := by
      simpa [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,registeredLink,setupLink,linkDevice] using fields
    obtain ⟨list,table⟩ := Prod.mk.inj empty
    simp [BaseCoherence.Inv,list,table]

theorem create_configured : Preserves ConfiguredIdentity.Inv wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have fields := congrArg (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) same
    rw [configured_link,configured_link] at fields
    exact fun s hs => hi s (fields.symm.trans hs)
  · have fields := congrArg (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) fresh
    rw [configured_link] at fields
    intro s hs
    rw [fields] at hs
    simp only [registeredLink,setupLink,Option.map_some,Option.some.injEq] at hs
    subst s
    constructor <;> simp [ConfiguredIdentity.state,linkDevice]

/-- Normal errno returns and successful creation both retain the supplied
entry. The fresh branch establishes empty structural/slot state directly. -/
theorem create : Preserves (Entry cs loans) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp HolderDeviceCreate.create w a result v b hi.1.1 run,
    (hoare_iff_run_ambient _ _ _).mp create_base w a result v b hi.1.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp create_configured w a result v b hi.1.2.2 run⟩,
    (hoare_iff_run_ambient _ _ _).mp HolderDeviceCreate.create_physical w a result v b hi.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp create_slots w a result v b hi.2.2 run⟩

private theorem base_socket {action : WG.M α} (same : SameSocket action) :
    SameView BaseCoherence.view action :=
  same.of_factor (fun s : WGOwnedView => BaseCoherence.view {dev:=s.dev}) _ (fun w => by
    simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,
      socketView,socketDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])

private theorem configured_socket {action : WG.M α} (same : SameSocket action) :
    Preserves ConfiguredIdentity.Inv action := by
  apply ConfiguredRemoval.frame
  apply same.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
  intro w
  simp only [ConfiguredIdentity.view,ConfiguredIdentity.state,socketView,socketDevice,
    wgOwnedView,wgStoreView,Option.map_map,Function.comp_def]
  rfl

theorem stop_base : SameView BaseCoherence.view wgStop := by
  intro initial
  change Preserves (fun w => BaseCoherence.view w=initial) _
  unfold wgStop purgeStagedPackets resetLastSentHandshake
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported,hiddenClock64]
  repeat' first
    | (rx_retention_head timersStop; exact (BaseCoherence.timersStop_view _).wp (fun s => s=initial))
    | (rx_retention_head handshakeClear; exact (BaseCoherence.handshakeClear_view _).wp (fun s => s=initial))
    | (rx_retention_head keypairsClear; exact (BaseCoherence.keypairsClear_view _).wp (fun s => s=initial))
    | (rx_retention_head socketReinit; exact (base_socket (socketReinit_sameSocket _ _)).wp (fun s => s=initial))
    | base_structure_step initial

theorem stop_configured : Preserves ConfiguredIdentity.Inv wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact ConfiguredRemoval.frame
        ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDevice.«0».Leanux.Proofs.WG.CurrentLifecycle.purgeStaged_view) _))
    | (rx_retention_head timersStop; exact ConfiguredRemoval.stopTimers _)
    | (rx_retention_head handshakeClear; exact ConfiguredRemoval.frame (ConfiguredMaintenance.handshakeClear_view _))
    | (rx_retention_head keypairsClear; exact ConfiguredRemoval.frame (ConfiguredMaintenance.keypairsClear_view _))
    | (rx_retention_head resetLastSentHandshake; exact ConfiguredRemoval.frame (ConfiguredIdentity.resetHandshake _))
    | (rx_retention_head socketReinit; exact configured_socket (socketReinit_sameSocket _ _))
    | configured_removal_step

private theorem purge_slots (pid : PeerId) : Preserves CurrentSlots.Inv (purgeStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  unfold purgeStagedPackets at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,ar,getter,run⟩ := run
  obtain ⟨same,time,d,hd,hp⟩ := getPeer_normal pid w read p a ar getter
  subst read
  subst ar
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,stats,as_,write,run⟩ := run
  cases write
  cases run
  apply CurrentSlots.fields_transport hi
  unfold CurrentSlots.fields RxCredits.keyWords
  simp only [hd,Option.map_some,Option.bind_some]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext q
  by_cases same : pid=q
  · subst q
    simp [hp,CurrentSlots.slotCell]
  · simp [Std.TreeMap.getElem?_insert,same]

theorem stop_slots : Preserves CurrentSlots.Inv wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact purge_slots _)
    | (rx_retention_head timersStop; exact CurrentSlots.Removal.stopTimers _)
    | (rx_retention_head handshakeClear; exact CurrentSlots.handshakeClear_preserves _)
    | (rx_retention_head keypairsClear; exact CurrentSlots.keypairsClear_preserves _)
    | (rx_retention_head resetLastSentHandshake; exact CurrentSlots.fields_preserves (project := id) (CurrentSlots.resetLastSentHandshake_fields _))
    | (rx_retention_head socketReinit; exact
        (pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.socket) (socketReinit_sameSocket _ _))
    | slot_remove_step

private theorem joined {action : WG.M α}
    (account : Preserves (Boundary cs loans) action)
    (base : SameView BaseCoherence.view action)
    (configured : Preserves ConfiguredIdentity.Inv action)
    (physical : SameView RxRing.nativeCell action)
    (slots : Preserves CurrentSlots.Inv action) : Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp account w a result v b hi.1.1 run,
    BaseCoherence.transport hi.1.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp base w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp configured w a result v b hi.1.2.2 run⟩,
    HolderStopPhysical.optional_cell hi.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp physical w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp slots w a result v b hi.2.2 run⟩

/-- Actual stop retains the supplied account and entry components through
its possibly deleting drains. No successful-record or pending-work assumption. -/
theorem stop : Preserves (Entry cs loans) wgStop :=
  joined HolderDeviceStop.stop stop_base stop_configured HolderStopPhysical.stop_cell stop_slots

theorem down_base : SameView BaseCoherence.view wgDown := by
  intro initial
  change Preserves (fun w => BaseCoherence.view w=initial) _
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop_base.wp (fun s => s=initial))
    | base_structure_step initial

theorem down_configured : Preserves ConfiguredIdentity.Inv wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop_configured)
    | configured_removal_step

theorem down_slots : Preserves CurrentSlots.Inv wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop_slots)
    | slot_remove_step

theorem down : Preserves (Entry cs loans) wgDown :=
  joined HolderDeviceStop.down down_base down_configured HolderStopPhysical.down_cell down_slots

private theorem keepalive_entry (pid : PeerId) :
    Preserves (DeviceBoundary.Entry cs loans) (sendKeepalive pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.join)
    (HolderTimers.keepalive_boundary pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.base_frame)
      (BaseCoherence.keepalive_view pid))
    (ConfiguredTraffic.keepalive pid)

/-- The saved open-time peer list drives the original staged-send/keepalive
loop; an actual socket errno returns before that loop. -/
theorem open_account : Preserves (DeviceBoundary.Entry cs loans) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact
        (pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.socket) (socketInit_sameSocket _))
    | (rx_retention_head sendStagedPackets; exact DeviceStages.staged _)
    | (rx_retention_head sendKeepalive; exact keepalive_entry _)
    | device_entry_step

theorem open_slots : Preserves CurrentSlots.Inv wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact
        (pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.socket) (socketInit_sameSocket _))
    | (rx_retention_head sendStagedPackets; exact CurrentSlots.sendStagedPackets_preserves _)
    | (rx_retention_head sendKeepalive; exact
        (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) _)
    | slot_remove_step

private theorem socketInit_cell (port : Nat) : SameView RxRing.nativeCell (socketInit port) :=
  (socketInit_sameSocket port).of_factor
    (fun s : WGOwnedView => s.dev.map fun d => (d.ifindex,d.decryptQueue)) RxRing.nativeCell
    (fun _ => by simp only [socketView,socketDevice,wgOwnedView,wgStoreView,RxRing.nativeCell,Option.map_map,Function.comp_def])

theorem open_cell : SameView RxRing.nativeCell wgOpen := by
  ring_cell_source [wgOpen] using [socketInit_cell,RxRing.sendStagedPackets_cell,RxRing.sendKeepalive_cell]

private theorem joined_entry {action : WG.M α}
    (account : Preserves (DeviceBoundary.Entry cs loans) action)
    (physical : SameView RxRing.nativeCell action)
    (slots : Preserves CurrentSlots.Inv action) : Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp account w a result v b hi.1 run,
    HolderStopPhysical.optional_cell hi.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp physical w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp slots w a result v b hi.2.2 run⟩

theorem open_preserves : Preserves (Entry cs loans) wgOpen :=
  joined_entry open_account open_cell open_slots

theorem up_account : Preserves (DeviceBoundary.Entry cs loans) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_account)
    | device_entry_step

theorem up_slots : Preserves CurrentSlots.Inv wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_slots)
    | slot_remove_step

theorem up_cell : SameView RxRing.nativeCell wgUp := by
  ring_cell_source [wgUp] using [open_cell]

/-- Both the successful open and its normal-error rollback retain the same
supplied entry components; no positive errno or successful-record premise. -/
theorem up : Preserves (Entry cs loans) wgUp :=
  joined_entry up_account up_cell up_slots

end Leanux.Proofs.WG.Queues.RxCredits.DeviceAuxEntry
