import Leanux.Proofs.WG.TransmitSecurity.BatchInitialized
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDriverCuts

/-! Resident batches keep one peer and one numeric key slot. This projection
is independent of key residency and allocation-stamped material continuity. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
variable {items : List SkbId} {w v : WGWorld} {pid : PeerId} {slot : KeypairId}

def Aligned (w : WGWorld) (pid : PeerId) (slot : KeypairId) (items : List SkbId) : Prop :=
  ∀ id ∈ items, ∀ packet, TxDisposition.txPackets w id = some packet →
    packet.peer = pid ∧ packet.keypair = slot

def Inv (w : WGWorld) : Prop :=
  ∀ pid p, peerAt w pid = some p → ∀ items ∈ p.txQueue.all, ∃ slot, Aligned w pid slot items

theorem Aligned.retains (before : Aligned w pid slot items)
    (packets : ∀ id packet, TxDisposition.txPackets v id = some packet →
      ∃ old, TxDisposition.txPackets w id = some old ∧
        PacketMaterial.material packet = PacketMaterial.material old) : Aligned v pid slot items := by
  intro id member packet resident
  obtain ⟨old,found,same⟩ := packets id packet resident
  have fields := before id member old found
  have peer : packet.peer = old.peer := by
    simpa only [PacketMaterial.material] using congrArg DataPacket.peer same
  have key : packet.keypair = old.keypair := by
    simpa only [PacketMaterial.material] using congrArg DataPacket.keypair same
  exact ⟨peer.trans fields.1,key.trans fields.2⟩

theorem Aligned.frame (before : Aligned w pid slot items)
    (same : PacketMaterial.view v = PacketMaterial.view w) : Aligned v pid slot items := by
  apply before.retains
  intro id packet resident
  have cell := congrFun same id
  simp only [PacketMaterial.view,resident,Option.map_some] at cell
  obtain ⟨old,found,material⟩ := Option.map_eq_some_iff.mp cell.symm
  exact ⟨old,found,material.symm⟩

theorem Inv.transport (before : Inv w)
    (queues : ∀ pid p, peerAt v pid = some p → ∀ items ∈ p.txQueue.all,
      ∃ old, peerAt w pid = some old ∧ items ∈ old.txQueue.all)
    (packets : ∀ id packet, TxDisposition.txPackets v id = some packet →
      ∃ old, TxDisposition.txPackets w id = some old ∧
        PacketMaterial.material packet = PacketMaterial.material old) : Inv v := by
  intro pid p found items member
  obtain ⟨old,resident,queued⟩ := queues pid p found items member
  obtain ⟨slot,aligned⟩ := before pid old resident items queued
  exact ⟨slot,aligned.retains packets⟩

theorem initial (net bare : Bool) : Inv (Runner.initialWG net bare) := by
  cases net <;> cases bare <;> simp [Inv,peerAt,Runner.initialWG]

theorem selected (before : Inv w) (physical : OccurrenceStack.Ready locals (items :: active) w) :
    ∃ pid slot, Aligned w pid slot items := by
  obtain ⟨pid,p,found,queued⟩ := physical.2.2.selected_owned
  obtain ⟨slot,aligned⟩ := before pid p found items queued
  exact ⟨pid,slot,aligned⟩

theorem Aligned.same_key (aligned : Aligned w pid slot items)
    (left : first ∈ items) (right : second ∈ items)
    (head : TxDisposition.txPackets w first = some headPacket)
    (packet : TxDisposition.txPackets w second = some dataPacket) :
    headPacket.keypair = dataPacket.keypair ∧ headPacket.peer = dataPacket.peer := by
  have h := aligned first left headPacket head
  have p := aligned second right dataPacket packet
  exact ⟨h.2.trans p.2.symm,h.1.trans p.1.symm⟩

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence
