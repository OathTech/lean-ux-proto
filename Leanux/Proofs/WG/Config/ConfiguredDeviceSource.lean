import Leanux.Proofs.WG.Config.ConfiguredDeviceLeavesSource
import Leanux.Proofs.WG.Index.ConfigurationKeyRulesSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem key_contracts (cs : Ledger) (loans : Reservations) :
    Index.ConfigurationKeyRules.Contracts (Entry cs loans) where
  read := get_ready
  identity key := join_ready cs loans _
    (Index.ConfigurationIndex.configuration_entry cs loans (setStaticIdentityPrivateKey_sameConfiguration key))
    (configuration_ready _ (setStaticIdentityPrivateKey_sameConfiguration key))
  cookie := join_ready cs loans _
    (Index.ConfigurationIndex.configuration_entry cs loans cookiePrecomputeDeviceKeys_sameConfiguration)
    (configuration_ready _ cookiePrecomputeDeviceKeys_sameConfiguration)
  precompute pid := join_ready cs loans _ (Index.ConfigurationIndex.precompute_entry cs loans pid)
    (precompute_ready pid)
  expire pid := join_ready cs loans _ (Index.ConfigurationIndex.expire_entry cs loans pid)
    (expire_ready pid)
  staged pid := join_ready cs loans _ (Index.ConfigurationIndex.staged_entry cs loans pid)
    (staged_ready pid)
  conflict key := join_ready cs loans _
    ((ensures_iff _ _ _).mp (Index.ConfigurationIndex.keyConflict cs loans key)) (conflict_ready key)

/-- Finite-list control with hypotheses only for actual saved members. -/
theorem forIn_members {α β : Type} (P : WGWorld → Prop) (xs : List α)
    (b : β) (action : α → β → WG.M (ForInStep β))
    (step : ∀ x∈xs,∀ b,Preserves P (action x b)) :
    Preserves P (forIn xs b action) := by
  induction xs generalizing b with
  | nil => rw [List.forIn_nil]; exact preserves_pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply preserves_bind (step x (by simp) b)
    intro result
    cases result with
    | done b => exact preserves_pure b
    | yield b => exact ih b (fun y hy=>step y (by simp [hy]))

theorem peers_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    Preserves (Entry cs loans) (Configuration.devicePeersSource attrs) := by
  rw [devicePeersSource_factor]
  unfold devicePeersWith
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply forIn_members (Entry cs loans)
       intro item member b
       cases item <;> dsimp only
       all_goals repeat' first
         | (rx_retention_head setPeerCmd; exact command_entry cs loans _ (shape _ member))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem privateKey_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    Preserves (Entry cs loans) (Configuration.deviceKeySource attrs) :=
  Index.ConfigurationKeyRules.key _ (key_contracts cs loans) attrs (peers_entry cs loans attrs shape)

theorem port_ready (port : Nat) : Preserves Ready (setPort port) := by
  unfold setPort
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head getDev; exact get_ready)
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_ready _)
    | (rx_retention_head socketInit; exact socket_ready _ (socketInit_sameSocket _))
    | (rx_retention_head modifyDev
       apply socket_ready
       intro initial
       exact modifyDev_socket_spec (fun s=>s=initial) _ (fun _=>rfl))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id Ready
       intro x b
       change Preserves Ready _)
    | rx_retention_step

theorem deviceUpdate_entry (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (shape : DeviceAddressShape attrs) (flags : UInt32) :
    Preserves (Entry cs loans) (Configuration.deviceUpdateSource attrs flags) := by
  rw [deviceUpdateSource_factor]
  unfold deviceUpdateWith
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head getDev; exact get_ready)
    | (rx_retention_head clearPeerEndpointSrc
       exact join_ready cs loans _ (Index.ConfigurationIndex.clearEndpoint_entry cs loans _) (clearEndpoint_ready _))
    | (rx_retention_head setPort
       exact join_ready cs loans _ (Index.ConfigurationIndex.port_entry cs loans _) (port_ready _))
    | (rx_retention_head peerRemoveAll
       exact join_ready cs loans _ (Index.ConfigurationIndex.bulk_entry cs loans) bulk_ready)
    | (rx_retention_head Configuration.deviceKeySource; exact privateKey_entry cs loans attrs shape)
    | (rx_retention_head modifyDev
       apply join_ready cs loans
       · apply Index.ConfigurationIndex.configuration_entry cs loans
         intro initial
         exact modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl)
       · apply configuration_ready
         intro initial
         exact modifyDev_configuration_spec (fun s=>s=initial) _ (fun _=>rfl))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Entry cs loans)
       intro x b
       change Preserves (Entry cs loans) _)
    | rx_retention_step

/-- Complete original device setter with actual guard order, conflict removal,
saved peer maintenance, replacement and member-indexed commands. Every normal
return retains the same-cut account and represented configured ownership. -/
theorem device_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) :
    Preserves (Entry cs loans) (wgSetDevice attrs) := by
  rw [←Configuration.wgSetDevice_source,setDeviceSource_factor]
  unfold setDeviceWith WG.orM
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Entry cs loans))
    | (rx_retention_head getDev; exact get_ready)
    | (rx_retention_head Configuration.deviceUpdateSource; exact deviceUpdate_entry cs loans attrs shape _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step


end Leanux.Proofs.WG.Config.OwnerConfiguration
