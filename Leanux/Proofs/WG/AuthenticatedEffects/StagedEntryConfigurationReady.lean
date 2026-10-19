import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationUpdate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationErasure
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleComplete

/-! Peer configuration derives creation freshness from the allocation
companion. Completed subcalls transport that companion through their exact
native counterpart, independently of the packet-history accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationReady
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver StackOwnership
open AllocatedCarrier
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem pure_checked (value : α) : Checked debts locals Safe (pure value) :=
  StatePrefixEnsures.pure value
    (fun h w _ before => by obtain ⟨ledger,entry⟩ := before.1; exact entrySafe ledger h w entry)
    (fun _ _ _ before => before)

theorem list {α β : Type} (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StatePrefixEnsures (Carrier debts locals) Safe
      (body item acc) (fun _ => Carrier debts locals)) :
    Checked debts locals Safe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ => Carrier debts locals) Safe
    (fun _ h w _ before => by obtain ⟨ledger,entry⟩ := before.1; exact entrySafe ledger h w entry) checked

theorem passive (action : WG.M α) (entry : SameView StagedEntry.view action)
    (allocated : Preserves Allocated action) : Checked debts locals Safe (liftWGPrefix action) :=
  pair Safe (SourcePassive.native Safe entrySafe action entry) (erasesStatePrefix_lift action) allocated

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Checked debts locals Safe (configOut hooks attrs peer ret) := by
  apply pair Safe (ConfigurationTail.out Safe entrySafe attrs peer ret) (ConfigurationErasure.out attrs peer ret)
  exact preserves_bind (AllocatedFrames.release peer) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.branch .peerZeroPsk attrs.presharedKey.isSome) _)
      (fun _ => preserves_pure ret))

variable (staging : ∀ pid, SourcePassive.Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, SourcePassive.Checked debts locals Safe (keepaliveObserved hooks pid))
include staging keepalive

theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Checked debts locals Safe (configTail hooks attrs peer pid) :=
  pair Safe (ConfigurationTail.tail Safe entrySafe staging keepalive attrs peer pid)
    (ConfigurationErasure.tail attrs peer pid)
    (AllocatedFrames.observed (peerConfigTailPrefix_erases attrs peer pid)
      (peerConfigTailPrefix_preserves allocationAmbient allocationConfigurationPeer attrs peer pid))

theorem update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Checked debts locals Safe (configUpdate hooks attrs peer flags psk pid) :=
  pair Safe (ConfigurationUpdate.update Safe entrySafe staging keepalive
    (LifecycleComplete.remove Safe entrySafe) attrs peer flags psk pid)
    (ConfigurationErasure.update attrs peer flags psk pid)
    (AllocatedFrames.observed (peerConfigUpdatePrefix_erases attrs peer flags psk pid)
      (peerConfigUpdatePrefix_preserves allocationAmbient allocationConfigurationPeer attrs peer flags psk pid))

macro "entry_allocated_frame" : tactic => `(tactic| (
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  try simp (config := {zeta := false}) only [WG.andM,WG.orM,branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head pubkeyLookup; exact (HandshakeLookup.public_lookup _).wp (· = initial))
    | (rx_retention_head peerGet; exact (Queued.acquire _).wp (· = initial))
    | entry_control_step initial))

macro "entry_allocation_frame" : tactic => `(tactic| (
  try simp (config := {zeta := false}) only [WG.andM,WG.orM,branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head pubkeyLookup; exact AllocatedFrames.public_lookup _)
    | (rx_retention_head peerGet; exact AllocatedFrames.acquire _)
    | (rx_retention_head getPeer; exact AllocatedFrames.read _)
    | (rx_retention_head getDev; exact AllocatedFrames.store getDev_sameWGStore)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step))

macro "entry_allocated_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_lift_action_head peerCreate; exact AllocatedCarrier.create $safe $entry _ _)
  | (maintenance_head liftWGPrefix
     apply passive $safe $entry
     · solve | entry_allocated_frame
     · solve | entry_allocation_frame)
  | (maintenance_head ForIn.forIn; apply list $safe $entry)
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem peer (attrs : PeerAttrs) : Checked debts locals Safe (configPeer hooks attrs) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (maintenance_head configOut; exact out Safe entrySafe _ _ _)
    | (maintenance_head configUpdate; exact update Safe entrySafe staging keepalive _ _ _ _ _)
    | entry_allocated_step Safe using entrySafe

theorem peers (attrs : DeviceAttrs) : Checked debts locals Safe (configPeers hooks attrs) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configPeers devicePeersWith
  repeat' first
    | (maintenance_head configPeer; exact peer Safe entrySafe staging keepalive _)
    | entry_allocated_step Safe using entrySafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationReady
