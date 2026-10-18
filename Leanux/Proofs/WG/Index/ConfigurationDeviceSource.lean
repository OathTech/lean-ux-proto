import Leanux.Proofs.WG.Index.ConfigurationPeersSource
import Leanux.Proofs.WG.Index.TimerCoreFrames
import Leanux.Proofs.WG.Index.BulkRemovalClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

open Queues.RxCredits.DurableHolders

theorem socket_entry {α : Type} (cs : Ledger) (loans : Reservations)
    {action : WG.M α} (same : SameSocket action) :
    Preserves (Entry cs loans) action := by
  apply join_entry cs loans action
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.socket) same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.socket) same)
  intro w a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp (frame_core (socket_fields same)) w a result v b pre.2 run

theorem clearEndpoint_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (clearPeerEndpointSrc pid) := by
  apply join_entry cs loans _ (DeviceStages.clearEndpoint pid) (CurrentSlots.Device.clearEndpoint pid)
  intro w a result v b pre run
  exact (TimerCore.endpoint pid w a result v b pre run).2

theorem bulk_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) peerRemoveAll := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  have post := peerRemoveAll_retirement_actual holders cs [] loans w a result v b
    ⟨pre.1.2.2,pre.1.2.1,funded,stable,
      fun d hd=>(pre.2.2 d hd).2.1,fun d hd=>(pre.2.2 d hd).2.2.1,
      fun d hd=>(pre.2.2 d hd).2.2.2⟩ run
  have tables := peerRemoveAll_tables w a result v b (fun d hd=>(pre.2.2 d hd).1) run
  have slots := (hoare_iff_run_ambient _ _ _).mp
    CurrentSlots.Removal.removeAll w a result v b pre.2.1 run
  obtain ⟨remaining,_,fundedOut,stableOut⟩ := post.account
  exact ⟨⟨⟨remaining,fundedOut,stableOut⟩,post.base,post.configured⟩,slots,
    fun d hd=>⟨tables d hd,post.covered d hd,post.coherent d hd,post.reserved d hd⟩⟩

theorem port_entry (cs : Ledger) (loans : Reservations) (port : Nat) :
    Preserves (Entry cs loans) (setPort port) := by
  unfold setPort
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head getDev; exact read_entry cs loans)
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_entry cs loans _)
    | (rx_retention_head socketInit; exact socket_entry cs loans (socketInit_sameSocket _))
    | (rx_retention_head modifyDev
       apply socket_entry cs loans
       intro initial
       exact modifyDev_socket_spec (fun s=>s=initial) _ (fun _=>rfl))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Entry cs loans)
       intro x b
       change Preserves (Entry cs loans) _)
    | rx_retention_step

theorem deviceUpdate_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) (flags : UInt32) :
    Preserves (Entry cs loans) (deviceUpdateSource attrs flags) := by
  rw [deviceUpdateSource_factor]
  unfold deviceUpdateWith
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head getDev; exact read_entry cs loans)
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_entry cs loans _)
    | (rx_retention_head setPort; exact port_entry cs loans _)
    | (rx_retention_head peerRemoveAll; exact bulk_entry cs loans)
    | (rx_retention_head deviceKeySource; exact privateKey_entry cs loans _)
    | (rx_retention_head modifyDev
       apply configuration_entry cs loans
       intro initial
       exact modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Entry cs loans)
       intro x b
       change Preserves (Entry cs loans) _)
    | rx_retention_step

/-- Every normal result of the complete original device setter retains the
same-cut account, configured/base identity, three-slot and index Core package.
The actual private-key conflict, replacement, and per-peer caller payments are
all composed; no future-state or successful-leaf premise is supplied. -/
theorem device_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Preserves (Entry cs loans) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source,setDeviceSource_factor]
  unfold setDeviceWith WG.orM
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Entry cs loans))
    | (rx_retention_head getDev; exact read_entry cs loans)
    | (rx_retention_head deviceUpdateSource; exact deviceUpdate_entry cs loans _ _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.Index.ConfigurationIndex
