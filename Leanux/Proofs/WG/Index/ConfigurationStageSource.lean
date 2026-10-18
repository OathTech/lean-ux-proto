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

macro "configuration_index_step" : tactic => `(tactic| first
  | (rx_retention_head getDev; exact read_entry _ _)
  | (rx_retention_head setStaticIdentityPrivateKey;
     exact configuration_entry _ _ (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys;
     exact configuration_entry _ _ cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact precompute_entry _ _ _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire_entry _ _ _)
  | (rx_retention_head sendStagedPackets; exact staged_entry _ _ _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Entry _ _))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Entry _ _)
     intro x b
     change Preserves (Entry _ _) _)
  | rx_retention_step)

theorem keyFinish_entry (cs : Ledger) (loans : Reservations) (key : Key) :
    Preserves (Entry cs loans)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' configuration_index_step

theorem keyChanged_entry (cs : Ledger) (loans : Reservations) (key : Key) :
    Preserves (Entry cs loans)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp (Entry cs loans))
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) (Entry cs loans))
  intro generated
  cases generated with
  | false => exact keyFinish_entry cs loans key
  | true =>
    cases pub with
    | none =>
      exact preserves_bind (hoare_liftAmbient
        (AmbientM.invariant "a generated public key without a write") (Entry cs loans))
        (fun _ => keyFinish_entry cs loans key)
    | some pub =>
      exact preserves_bind ((ensures_iff _ _ _).mp (keyConflict cs loans pub))
        (fun _ => keyFinish_entry cs loans key)

theorem key_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (peers : Preserves (Entry cs loans) (devicePeersSource attrs)) :
    Preserves (Entry cs loans) (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | exact peers
    | configuration_index_step
  all_goals exact keyChanged_entry _ _ _

end Leanux.Proofs.WG.Index.ConfigurationIndex
