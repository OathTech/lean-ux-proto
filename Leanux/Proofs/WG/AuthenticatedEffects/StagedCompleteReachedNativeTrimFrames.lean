import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontResidualPath
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeCurrent

/-! Native trim writes change the staged cohort and drop counter while
retaining the allocated cell map, allocation bounds and owning queues. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Staged.Origins Staged.Obligations RetirementSecurity AllocatedObligation CausalJournal

def packetView (w : WGWorld) :=
  (Packets.epoch w,PacketMaterial.view w,Packets.snapshot w,TxDisposition.txPackets w,txQueueContents w)

theorem dropped_packets (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    packetView (droppedWorld pid p d w)=packetView w := by
  apply Prod.ext
  · simp [packetView,Packets.epoch,droppedWorld,device]
  apply Prod.ext
  · funext id
    simp [packetView,PacketMaterial.view,TxDisposition.txPackets,droppedWorld,device]
  apply Prod.ext
  · simp [packetView,Packets.snapshot,Packets.deviceStore,droppedWorld,device]
  apply Prod.ext
  · funext id
    simp [packetView,TxDisposition.txPackets,droppedWorld,device]
  change txQueueContents (droppedWorld pid p d w)=txQueueContents w
  funext owner
  by_cases same : pid=owner
  · subst owner
    simp [txQueueContents,Queues.RxCredits.handoffTxView,droppedWorld,device,resident]
  · simp [txQueueContents,Queues.RxCredits.handoffTxView,droppedWorld,device,Std.TreeMap.getElem?_insert,same]

theorem charged_packets (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    packetView (chargedWorld pid p d w)=packetView w := by
  have same : packetView (chargedWorld pid p d w)=packetView (droppedWorld pid p d w) := rfl
  exact same.trans (dropped_packets device resident)

theorem Yields.packets (path : Yields pid w a n v b) : packetView v=packetView w := by
  induction path with
  | zero=>rfl
  | step path next ih=>
      obtain ⟨d,p,device,resident,_,rfl,_⟩:=body_yield next
      exact (charged_packets device resident).trans ih

theorem Yields.staged_packets (path : Yields pid w a n v b)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (generation : Nat) (owner : PeerId) (stamp : Nat) :
    stagedPackets generation owner stamp v=
      (stagedPackets generation owner stamp w).drop (if owner=pid then n else 0) := by
  have epoch:=congrArg Prod.fst path.packets
  change Packets.epoch v=Packets.epoch w at epoch
  by_cases same : owner=pid
  · subst owner
    have initial : Staged.stagedAt w pid=some (p.internalId,p.staged) := by
      simp [Staged.stagedAt,device,resident]
    simp only [stagedPackets,epoch,(path.geometry device resident).2.1,initial,ite_true]
    split <;> (try split) <;> simp only [List.drop_nil]
  · simp only [stagedPackets,epoch,(path.geometry device resident).2.2.2 owner (Ne.symm same),
      same,ite_false,List.drop_zero]

theorem TrimCut.dropped_staged_packets (cut : TrimCut h ledger debts locals pid w a n v b)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p)
    (excess : p.staged.length>MAX_STAGED_PACKETS)
    (generation : Nat) (owner : PeerId) (stamp : Nat) :
    stagedPackets generation owner stamp (droppedWorld pid p d v)=
      (stagedPackets generation owner stamp w).drop (if owner=pid then n+1 else 0) := by
  have next:= (cut.drop_cut device resident excess).2.2
  obtain ⟨initial,old,original,oldPeer⟩:=cut.read
  have equal : stagedPackets generation owner stamp (droppedWorld pid p d v)=
      stagedPackets generation owner stamp (chargedWorld pid p d v) := rfl
  exact equal.trans (next.staged_packets original oldPeer generation owner stamp)

theorem packet_frame (before : NativeReady.Inv locals w) (physical : Staged.Obligations.Physical h ledger debts w)
    (same : packetView v=packetView w) : NativeReady.Inv locals v ∧ Staged.Obligations.Physical h ledger debts v := by
  have epoch:=congrArg Prod.fst same
  have material:=congrArg (fun x=>x.2.1) same
  have snapshot : Packets.snapshot v=Packets.snapshot w:=congrArg (fun x=>x.2.2.1) same
  have packets:=congrArg (fun x=>x.2.2.2.1) same
  have owners:=congrArg (fun x=>x.2.2.2.2) same
  refine ⟨⟨?_,before.2.1.cells packets owners,before.2.2.queueContents owners packets⟩,
    physical.views epoch material⟩
  simpa only [Packets.Inv,snapshot] using before.1

theorem TrimCut.packet_account (cut : TrimCut h ledger debts locals pid w a n v b) :
    NativeReady.Inv locals v ∧ Staged.Obligations.Physical h ledger debts v :=
  packet_frame (NativeAccounting.Current.of_accounted cut.entry).native cut.entry.entry.core.physical cut.path.packets

theorem TrimCut.dropped_packet_account (cut : TrimCut h ledger debts locals pid w a n v b)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p) :
    NativeReady.Inv locals (droppedWorld pid p d v) ∧
      Staged.Obligations.Physical h ledger debts (droppedWorld pid p d v) :=
  packet_frame cut.packet_account.1 cut.packet_account.2 (dropped_packets device resident)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual

