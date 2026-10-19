import Leanux.Proofs.WG.Index.ConfigurationKeyRulesSource
import Leanux.Proofs.WG.Index.ConfigurationIndexFrames
import Leanux.Proofs.WG.Index.ConfigurationLoanSource
import Leanux.Proofs.WG.Index.ExpiryIndexClaims
import Leanux.Proofs.WG.Index.StagingIndexClaims
import Leanux.Proofs.WG.Config.ClearedSources

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem join_entry {α : Type} (cs : Ledger) (loans : Reservations) (action : WG.M α)
    (account : Preserves (DeviceBoundary.Entry cs loans) action)
    (slots : Preserves CurrentSlots.Inv action)
    (core : Ensures action (fun w => CurrentSlots.Inv w ∧ Reached.Core w) (fun _ => Reached.Core)) :
    Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp account w a result v b pre.1 run,
    (hoare_iff_run_ambient _ _ _).mp slots w a result v b pre.2.1 run,
    core w a result v b pre.2 run⟩

theorem configuration_entry {α : Type} (cs : Ledger) (loans : Reservations)
    {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Entry cs loans) action := by
  apply join_entry cs loans action
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.configuration) same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.configuration) same)
  intro w a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp (frame_core (configuration_fields same))
    w a result v b pre.2 run

theorem precompute_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (precomputeStaticStatic pid) := by
  apply join_entry cs loans _ (DeviceStages.precompute pid)
    (CurrentSlots.fields_preserves (project:=id) (CurrentSlots.precomputeStaticStatic_fields pid))
  intro w a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp (frame_core (precompute_fields pid))
    w a result v b pre.2 run

theorem expire_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (expireCurrentPeerKeypairs pid) := by
  apply join_entry cs loans _ (DeviceStages.expire pid)
    (CurrentSlots.expireCurrentPeerKeypairs_preserves pid)
  intro w a result v b pre run
  exact expireCurrentPeerKeypairs_indexCore pid w a result v b pre.2 run

theorem staged_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (sendStagedPackets pid) :=
  join_entry cs loans _ (DeviceStages.staged pid)
    (CurrentSlots.sendStagedPackets_preserves pid) (StagingRich.staged_core pid)

theorem keyContracts (cs : Ledger) (loans : Reservations) :
    ConfigurationKeyRules.Contracts (Entry cs loans) where
  read := read_entry cs loans
  identity key := configuration_entry cs loans (setStaticIdentityPrivateKey_sameConfiguration key)
  cookie := configuration_entry cs loans cookiePrecomputeDeviceKeys_sameConfiguration
  precompute := precompute_entry cs loans
  expire := expire_entry cs loans
  staged := staged_entry cs loans
  conflict key := (ensures_iff _ _ _).mp (keyConflict cs loans key)

theorem keyFinish_entry (cs : Ledger) (loans : Reservations) (key : Key) :
    Preserves (Entry cs loans)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) :=
  ConfigurationKeyRules.keyFinish _ (keyContracts cs loans) key

theorem keyChanged_entry (cs : Ledger) (loans : Reservations) (key : Key) :
    Preserves (Entry cs loans)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) :=
  ConfigurationKeyRules.keyChanged _ (keyContracts cs loans) key

theorem key_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (peers : Preserves (Entry cs loans) (devicePeersSource attrs)) :
    Preserves (Entry cs loans) (deviceKeySource attrs) :=
  ConfigurationKeyRules.key _ (keyContracts cs loans) attrs peers

end Leanux.Proofs.WG.Index.ConfigurationIndex
