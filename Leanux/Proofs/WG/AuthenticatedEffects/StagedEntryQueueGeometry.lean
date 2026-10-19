import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCarrier

/-! Queue contents, rather than the existence of an empty peer allocation,
determine pending staged obligations. Fresh empty peers may change the resident
peer map without changing any packet's obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.QueueGeometry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity

def queues (w : WGWorld) := fun epoch pid stamp => stagedPackets epoch pid stamp w

theorem of_view {action : WG.M α} (frame : SameView StagedEntry.view action) :
    SameView queues action := by
  exact frame.of_factor
    (fun s => fun epoch pid stamp => if s.1 = some epoch then
      match s.2.1 pid with
      | none => []
      | some (allocation,packets) => if allocation = stamp then packets else []
      else []) queues (fun _ => rfl)

theorem transport (before : Inv history ledger debts locals w)
    (epoch : Packets.epoch v = Packets.epoch w) (staged : queues v = queues w)
    (cells : TxDisposition.txPackets v = TxDisposition.txPackets w)
    (snapshot : Packets.snapshot v = Packets.snapshot w)
    (owners : txQueueContents v = txQueueContents w) : Inv history ledger debts locals v := by
  have material : PacketMaterial.view v = PacketMaterial.view w := by
    funext id
    simp only [PacketMaterial.view,cells]
  refine ⟨⟨before.core.valid,?_,before.core.selected,before.core.physical.views epoch material⟩,
    before.justified,before.allocationLinks,before.noSelected,?_,
    before.coverage.cells cells owners,before.inventory.queueContents owners cells⟩
  · intro generation pid stamp
    have same := congrFun (congrFun (congrFun staged generation) pid) stamp
    change stagedPackets generation pid stamp v = stagedPackets generation pid stamp w at same
    rw [same]
    exact before.core.queues generation pid stamp
  · simpa only [Packets.Inv,snapshot] using before.packets

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.QueueGeometry
