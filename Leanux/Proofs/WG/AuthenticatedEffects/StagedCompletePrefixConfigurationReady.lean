import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationAllocated
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixConfigurationUpdate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationErasure
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationReady

/-! Peer configuration derives creation freshness from the allocation
companion. Completed subcalls transport that companion through their exact
native counterpart, independently of the packet-history accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationReady
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver StackOwnership
open CompleteAllocated (Carrier)
open ConfigurationAllocated
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Checked debts locals Safe (configOut hooks attrs peer ret) := by
  apply pair Safe (ConfigurationTail.out Safe accountSafe attrs peer ret) (ConfigurationErasure.out attrs peer ret)
  exact preserves_bind (AllocatedFrames.release peer) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.branch .peerZeroPsk attrs.presharedKey.isSome) _)
      (fun _ => preserves_pure ret))

variable (staging : ∀ pid, Passive.Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, Passive.Checked debts locals Safe (keepaliveObserved hooks pid))
include staging keepalive

theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Checked debts locals Safe (configTail hooks attrs peer pid) :=
  pair Safe (ConfigurationTail.tail Safe accountSafe staging keepalive attrs peer pid)
    (ConfigurationErasure.tail attrs peer pid)
    (AllocatedFrames.observed (peerConfigTailPrefix_erases attrs peer pid)
      (peerConfigTailPrefix_preserves allocationAmbient allocationConfigurationPeer attrs peer pid))

variable (drained : ∀ upTo, Passive.Checked debts locals Safe (sendDrainObserved hooks upTo))
include drained

theorem update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Checked debts locals Safe (configUpdate hooks attrs peer flags psk pid) :=
  pair Safe (ConfigurationUpdate.update Safe accountSafe staging keepalive
    (Lifecycle.remove Safe accountSafe drained) attrs peer flags psk pid)
    (ConfigurationErasure.update attrs peer flags psk pid)
    (AllocatedFrames.observed (peerConfigUpdatePrefix_erases attrs peer flags psk pid)
      (peerConfigUpdatePrefix_preserves allocationAmbient allocationConfigurationPeer attrs peer flags psk pid))

macro "prefix_allocated_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_lift_action_head peerCreate; exact ConfigurationAllocated.create $safe $entry _ _)
  | (maintenance_head liftWGPrefix
     apply passive $safe $entry
     · solve | entry_allocated_frame
     · solve | entry_allocation_frame)
  | (maintenance_head ForIn.forIn; apply list $safe)
  | (maintenance_head Pure.pure; exact pure_checked $safe _)
  | (maintenance_head Bind.bind; apply StateEnsures.bind (Q := fun _ => Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem peer (attrs : PeerAttrs) : Checked debts locals Safe (configPeer hooks attrs) := by
  change StateEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (maintenance_head configOut; exact out Safe accountSafe _ _ _)
    | (maintenance_head configUpdate; exact update Safe accountSafe staging keepalive drained _ _ _ _ _)
    | prefix_allocated_step Safe using accountSafe

theorem peers (attrs : DeviceAttrs) : Checked debts locals Safe (configPeers hooks attrs) := by
  change StateEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configPeers devicePeersWith
  repeat' first
    | (maintenance_head configPeer; exact peer Safe accountSafe staging keepalive drained _)
    | prefix_allocated_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationReady
