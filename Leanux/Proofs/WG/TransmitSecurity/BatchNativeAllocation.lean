import Leanux.Proofs.WG.TransmitSecurity.BatchNativeKeys
import Leanux.Proofs.WG.TransmitSecurity.PacketAllocation

/-! Native allocation preserves old queued batches using their actual physical
residency and creates a homogeneous new batch from the staged arguments. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option pp.structureInstances false

/-- Previously queued cells are below the allocator's frontier. Their material
is retained even though allocation extends the TX table. -/
theorem allocate_old (before : Inv w) (inventory : TxInventory locals w)
    (bounded : Packets.Inv w) (packets : List DataPacket)
    (a b : Ambient) (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    Inv v := by
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter packets) w a items v b run
  have peers : peersAt v = peersAt w := congrArg (fun fields => fields.2.1) perimeter
  have cells : ∀ pid, peerAt v pid = peerAt w pid := by
    intro pid
    simpa [peerAt,peersAt,Option.bind_map,Function.comp_def] using
      congrArg (fun entries => entries.bind fun table => table[pid]?) peers
  intro pid p resident batch member
  have oldPeer := (cells pid).symm.trans resident
  obtain ⟨slot,old⟩ := before pid p oldPeer batch member
  refine ⟨slot,?_⟩
  intro id inside packet found
  obtain ⟨previous,atEntry⟩ := inventory.queueResident pid p oldPeer id
    (List.mem_flatten.mpr ⟨batch,member,inside⟩)
  have atEnd := (TxDisposition.ItemSeparation.allocate_resident bounded atEntry run).2
  have same : previous = packet := Option.some.inj (atEnd.symm.trans found)
  subst packet
  exact old id inside previous atEntry

/-- The exact returned allocation positions contain the corresponding staged
packet; common peer/key fields therefore transfer to the whole returned list. -/
theorem allocate_aligned (packets : List DataPacket)
    (shape : BatchHistory.Aligned pid slot packets) (device : w.dev = some d)
    (a b : Ambient) (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    Aligned v pid slot items := by
  intro id member packet found
  obtain ⟨n,atItem⟩ := List.mem_iff_getElem?.mp member
  have sizes : items.length = packets.length := by
    rw [(TxDisposition.ItemSeparation.allocate_result packets device run).1,List.length_range']
  have below : n < packets.length := by
    rw [← sizes]
    exact List.getElem?_eq_some_iff.mp atItem |>.1
  let input := packets[n]
  have atInput : packets[n]? = some input := List.getElem?_eq_getElem below
  obtain ⟨actual,position,resident⟩ := PacketAllocation.records packets device run n input atInput
  have same : actual = id := Option.some.inj (position.symm.trans atItem)
  subst actual
  have equal : input = packet := Option.some.inj (resident.symm.trans found)
  exact equal ▸ shape input (List.mem_of_getElem? atInput)

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
