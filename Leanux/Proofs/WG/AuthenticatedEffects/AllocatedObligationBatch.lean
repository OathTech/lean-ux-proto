import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationSettlement

/-! Connect the same fixed incoming ticket list to the native allocation
ordinals. This bridge does not choose fresh existential tickets or infer
queue/held ownership merely from the existence of a resident packet cell. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

theorem aligned_at {related : α → β → Prop} {tickets : List α} {packets : List β}
    {ordinal : Nat} {ticket : α} (aligned : Aligned related tickets packets)
    (atTicket : tickets[ordinal]? = some ticket) :
    ∃ packet, packets[ordinal]? = some packet ∧ related ticket packet := by
  induction aligned generalizing ordinal with
  | nil => simp at atTicket
  | cons relation rest ih =>
    cases ordinal with
    | zero =>
      have same := Option.some.inj atTicket
      subst ticket
      exact ⟨_,rfl,relation⟩
    | succ ordinal => exact ih atTicket

/-- Each incoming fixed ticket keeps its own ordinal, native allocated ID,
packet material and input relation. Identical packet values cannot substitute
another ticket for it. The allocation receipt is at the actual appended cut. -/
theorem allocated_ticket (history : List CausalJournal.Event) (packets : List DataPacket)
    (run : WGRunWitness (List SkbId)) (valid : run.Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d)
    (aligned : Aligned related tickets packets) (atTicket : tickets[ordinal]? = some ticket) :
    ∃ packet id,
      packets[ordinal]? = some packet ∧ related ticket packet ∧
      run.value[ordinal]? = some id ∧
      Origin (history ++ [.old (.allocated packets run)]) history.length ordinal
        d.ifindex id (PacketMaterial.material packet) ∧
      PacketMaterial.view run.after id = some (PacketMaterial.material packet) ∧
      packetStamp run.after id = (d.ifindex,id+1) := by
  obtain ⟨packet,payload,relation⟩ := aligned_at aligned atTicket
  obtain ⟨id,cellAt,cell⟩ := PacketAllocation.records packets device valid ordinal packet payload
  obtain ⟨_,_,after,afterDevice,_,epoch,_⟩ := TxDisposition.ItemSeparation.allocate_result packets device valid
  have generation : Packets.epoch run.after = some d.ifindex := by
    simp [Packets.epoch,afterDevice,epoch]
  refine ⟨packet,id,payload,relation,cellAt,?_,?_,?_⟩
  · exact ⟨packets,run,packet,by simp,valid,generation,payload,cellAt,rfl⟩
  · simp only [PacketMaterial.view,cell,Option.map_some]
  · simp [packetStamp,afterDevice,epoch]

/-- A new batch is disjoint from every already backed pending cell, using
the existing native packet-frontier invariant. This is allocation separation,
not proof that every resident cell is owned by a queue or active continuation. -/
theorem allocated_fresh_of_backed
    (backed : Backed history position ordinal run.before)
    (bounded : Packets.Inv run.before) (packets : List DataPacket)
    (valid : (run : WGRunWitness (List SkbId)).Valid (packets.mapM newTxSkb)) :
    ∃ generation id value,
      Origin history position ordinal generation id value ∧
      Packets.epoch run.before = some generation ∧
      PacketMaterial.view run.before id = some value ∧ id ∉ run.value ∧
      PacketMaterial.view run.after id = some value := by
  obtain ⟨generation,id,value,origin,epoch,cell⟩ := backed
  obtain ⟨packet,resident,material⟩ := Option.map_eq_some_iff.mp cell
  obtain ⟨fresh,kept⟩ := TxDisposition.ItemSeparation.allocate_resident bounded resident valid
  refine ⟨generation,id,value,origin,epoch,cell,fresh,?_⟩
  simp only [PacketMaterial.view,kept,Option.map_some,material]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
