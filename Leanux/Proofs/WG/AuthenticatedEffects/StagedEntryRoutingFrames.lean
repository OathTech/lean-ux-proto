import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryControlFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryZeroTimer
import Leanux.Proofs.WG.TransmitSecurity.StagedAllowedIpFrames

/-! Allowed-IP edits and marking a peer dead preserve its staged and TX
owners. Actual disposal and reference repayment have separate source rules. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RoutingFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem aip (action : AipM α) : SameView StagedEntry.view (liftAip action) := by
  intro initial
  apply hoare_liftAip
  intro w d table before device
  rw [← before]
  unfold StagedEntry.view
  apply Prod.ext
  · simp [Packets.epoch,device]
  apply Prod.ext
  · funext pid; simp [Staged.stagedAt,device]
  apply Prod.ext
  · funext skb; simp [PacketMaterial.view,TxDisposition.txPackets,device]
  apply Prod.ext
  · simp [Packets.snapshot,Packets.deviceStore,device]
  apply Prod.ext
  · funext skb; simp [TxDisposition.txPackets,device]
  · funext pid; simp [txQueueContents,handoffTxView,device]

theorem list_add (pid : PeerId) (node : NodeId) : SameView StagedEntry.view (listAddTail pid node) := by
  unfold listAddTail
  apply Queued.update
  intro p
  exact ⟨rfl,rfl,rfl⟩

theorem list_factor (w : WGWorld) :
    StagedEntry.view w = ZeroTimer.fromBorrow (AllowedIps.clearListView w) := by
  cases device : w.dev <;>
    simp [Function.comp_def,funext_iff,ZeroTimer.fromBorrow,StagedEntry.view,AllowedIps.clearListView,wgStoreView,
      Packets.epoch,Staged.stagedAt,PacketMaterial.view,TxDisposition.txPackets,
      Packets.snapshot,Packets.deviceStore,txQueueContents,handoffTxView,device]

theorem list_delete (node : NodeId) : SameView StagedEntry.view (listDel node) :=
  (AllowedIps.listDel_clearListView node).of_factor ZeroTimer.fromBorrow StagedEntry.view list_factor

theorem node {action : WG.M α} (same : SameNode action) : SameView StagedEntry.view action := by
  exact same.of_factor (fun s => StagedEntry.view {dev := s.dev}) StagedEntry.view
    (fun w => by cases device : w.dev <;>
      simp [funext_iff,StagedEntry.view,nodeView,nodeDevice,wgStoreView,
        Packets.epoch,Staged.stagedAt,PacketMaterial.view,TxDisposition.txPackets,
        Packets.snapshot,Packets.deviceStore,txQueueContents,handoffTxView,device])

macro "entry_routing_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head branch; exact (TimerFrames.branch_frame _ _).wp (· = $initial))
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact (aip _).wp (· = $initial))
  | (rx_retention_head liftAip; exact (aip _).wp (· = $initial))
  | (rx_retention_head listAddTail; exact (list_add _ _).wp (· = $initial))
  | (rx_retention_head listDel; exact (list_delete _).wp (· = $initial))
  | entry_control_step $initial)

theorem add (root : Leanux.WG.Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView StagedEntry.view (Leanux.WG.add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold Leanux.WG.add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' entry_routing_step initial

theorem insert (family addr cidr : Nat) (pid : PeerId) :
    SameView StagedEntry.view (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head WG.add; exact (add _ _ _ _ _).wp (· = initial))
    | entry_routing_step initial

theorem set (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView StagedEntry.view (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (insert _ _ _ _).wp (· = initial))
    | entry_routing_step initial

theorem remove (pid : PeerId) : SameView StagedEntry.view (removeByPeer pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head AllowedIps.removeNodeBody; exact (node (removeNodeBody_sameNode _)).wp (· = initial))
    | entry_routing_step initial

theorem store_factor (w : WGWorld) :
    StagedEntry.view w = ZeroTimer.fromBorrow (AllowedIps.clearStoreView w) := by
  cases device : w.dev <;>
    simp [Function.comp_def,funext_iff,ZeroTimer.fromBorrow,StagedEntry.view,AllowedIps.clearStoreView,
      AllowedIps.clearStoreProjection,wgStoreView,Packets.epoch,Staged.stagedAt,
      PacketMaterial.view,TxDisposition.txPackets,Packets.snapshot,Packets.deviceStore,
      txQueueContents,handoffTxView,device]

theorem free : SameView StagedEntry.view WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have fields := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  rw [store_factor v,fields]
  cases device : w.dev <;>
    simp [Function.comp_def,funext_iff,ZeroTimer.fromBorrow,StagedEntry.view,AllowedIps.clearStoreProjection,
      AllowedIps.resetAllowedips,wgStoreView,Packets.epoch,Staged.stagedAt,
      PacketMaterial.view,TxDisposition.txPackets,Packets.snapshot,Packets.deviceStore,
      txQueueContents,handoffTxView,device]

theorem make_dead (pid : PeerId) : SameView StagedEntry.view (peerMakeDead pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact (remove _).wp (· = initial))
    | entry_control_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RoutingFrames
