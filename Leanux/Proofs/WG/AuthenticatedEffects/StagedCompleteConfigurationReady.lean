import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationUpdate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationErasure
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationReady

/-! Peer configuration derives creation freshness from the allocation
companion. Completed subcalls transport that companion through their exact
native counterpart, independently of the packet-history accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConfigurationReady
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver StackOwnership
open CompleteAllocated
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem pure_checked (value : α) : Checked debts locals Safe (pure value) :=
  StatePrefixEnsures.pure value
    (fun h w _ before => by obtain ⟨ledger,entry⟩ := before.1; exact accountSafe ledger h w entry)
    (fun _ _ _ before => before)

theorem list {α β : Type} (xs : List α) (initial : β) (body : α → β → WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StatePrefixEnsures (Carrier debts locals) Safe
      (body item acc) (fun _ => Carrier debts locals)) :
    Checked debts locals Safe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ => Carrier debts locals) Safe
    (fun _ h w _ before => by obtain ⟨ledger,entry⟩ := before.1; exact accountSafe ledger h w entry) checked

theorem passive (action : WG.M α) (entry : SameView StagedEntry.view action)
    (allocated : Preserves Allocated action) : Checked debts locals Safe (liftWGPrefix action) :=
  pair Safe (CompletePassive.native Safe accountSafe action entry) (erasesStatePrefix_lift action) allocated

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    Checked debts locals Safe (configOut hooks attrs peer ret) := by
  apply pair Safe (CompleteConfigurationTail.out Safe accountSafe attrs peer ret) (ConfigurationErasure.out attrs peer ret)
  exact preserves_bind (AllocatedFrames.release peer) (fun _ =>
    preserves_bind (hoare_liftAmbient (AmbientM.branch .peerZeroPsk attrs.presharedKey.isSome) _)
      (fun _ => preserves_pure ret))

variable (staging : ∀ pid, CompletePassive.Checked debts locals Safe (stagingObserved hooks pid))
variable (keepalive : ∀ pid, CompletePassive.Checked debts locals Safe (keepaliveObserved hooks pid))
include staging keepalive

theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Checked debts locals Safe (configTail hooks attrs peer pid) :=
  pair Safe (CompleteConfigurationTail.tail Safe accountSafe staging keepalive attrs peer pid)
    (ConfigurationErasure.tail attrs peer pid)
    (AllocatedFrames.observed (peerConfigTailPrefix_erases attrs peer pid)
      (peerConfigTailPrefix_preserves allocationAmbient allocationConfigurationPeer attrs peer pid))

theorem update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Checked debts locals Safe (configUpdate hooks attrs peer flags psk pid) :=
  pair Safe (CompleteConfigurationUpdate.update Safe accountSafe staging keepalive
    (CompleteLifecycle.remove Safe accountSafe) attrs peer flags psk pid)
    (ConfigurationErasure.update attrs peer flags psk pid)
    (AllocatedFrames.observed (peerConfigUpdatePrefix_erases attrs peer flags psk pid)
      (peerConfigUpdatePrefix_preserves allocationAmbient allocationConfigurationPeer attrs peer flags psk pid))

macro "complete_allocated_step " safe:term " using " entry:term : tactic => `(tactic| first
  | (maintenance_lift_action_head peerCreate; exact CompleteAllocated.create $safe $entry _ _)
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
    | (maintenance_head configOut; exact out Safe accountSafe _ _ _)
    | (maintenance_head configUpdate; exact update Safe accountSafe staging keepalive _ _ _ _ _)
    | complete_allocated_step Safe using accountSafe

theorem peers (attrs : DeviceAttrs) : Checked debts locals Safe (configPeers hooks attrs) := by
  change StatePrefixEnsures (Carrier debts locals) Safe _ (fun _ => Carrier debts locals)
  unfold configPeers devicePeersWith
  repeat' first
    | (maintenance_head configPeer; exact peer Safe accountSafe staging keepalive _)
    | complete_allocated_step Safe using accountSafe

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteConfigurationReady
