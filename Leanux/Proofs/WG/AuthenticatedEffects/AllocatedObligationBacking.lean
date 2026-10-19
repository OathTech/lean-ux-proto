import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSettlement
import Leanux.Proofs.WG.TransmitSecurity.PacketOrigins

/-! Physical backing for pending allocated obligations. The source position
and ordinal identify an actual allocation, while its epoch and resident cell
prevent a disappeared packet from remaining merely an abstract pending token.
This is a local carrier interface, not an initialized conservation theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
variable {id : Nat}

/-- An exact allocation position and ordinal, with immutable packet material.
Scheduling state and ciphertext may subsequently change in the resident cell. -/
def Origin (history : List CausalJournal.Event) (position ordinal generation id : Nat)
    (value : DataPacket) : Prop :=
  ∃ (packets : List DataPacket) (run : WGRunWitness (List SkbId)) (packet : DataPacket),
    history[position]? = some (.old (.allocated packets run)) ∧
    run.Valid (packets.mapM newTxSkb) ∧ Packets.epoch run.after = some generation ∧
    packets[ordinal]? = some packet ∧ run.value[ordinal]? = some id ∧
    PacketMaterial.material packet = value

def Backed (history : List CausalJournal.Event) (position ordinal : Nat) (w : WGWorld) : Prop :=
  ∃ generation id value, Origin history position ordinal generation id value ∧
    Packets.epoch w = some generation ∧ PacketMaterial.view w id = some value

/-- Every pending allocated entry is backed, including entries no longer in a
native queue but still held by a completion or disposal continuation. -/
def Resident (history : List CausalJournal.Event) (ledger : Ledger) (w : WGWorld) : Prop :=
  ∀ ticket position ordinal, (ticket,Status.pending (.allocated position ordinal)) ∈ ledger →
    Backed history position ordinal w

theorem Origin.position_lt (origin : Origin history position ordinal generation id value) :
    position < history.length := by
  obtain ⟨packets,run,packet,atPosition,rest⟩ := origin
  exact List.getElem?_eq_some_iff.mp atPosition |>.1

theorem Origin.append (origin : Origin history position ordinal generation id value)
    (suffix : List CausalJournal.Event) :
    Origin (history ++ suffix) position ordinal generation id value := by
  have below := origin.position_lt
  obtain ⟨packets,run,packet,atPosition,valid,epoch,payload,cell,material⟩ := origin
  exact ⟨packets,run,packet,by simpa [List.getElem?_append_left below] using atPosition,
    valid,epoch,payload,cell,material⟩

/-- A position/ordinal cannot designate two different packet allocations,
even if the plaintexts or numeric IDs happen to be equal elsewhere. -/
theorem Origin.unique (first : Origin history position ordinal generation id value)
    (second : Origin history position ordinal otherGeneration otherId otherValue) :
    generation = otherGeneration ∧ id = otherId ∧ value = otherValue := by
  obtain ⟨packets,run,packet,atPosition,_,epoch,payload,cell,material⟩ := first
  obtain ⟨otherPackets,otherRun,otherPacket,otherAt,_,otherEpoch,otherPayload,otherCell,otherMaterial⟩ := second
  have same := Option.some.inj (atPosition.symm.trans otherAt)
  cases same
  have samePacket := Option.some.inj (payload.symm.trans otherPayload)
  subst otherPacket
  exact ⟨Option.some.inj (epoch.symm.trans otherEpoch),
    Option.some.inj (cell.symm.trans otherCell),material.symm.trans otherMaterial⟩

theorem Backed.append (backed : Backed history position ordinal w)
    (suffix : List CausalJournal.Event) : Backed (history ++ suffix) position ordinal w := by
  obtain ⟨generation,id,value,origin,epoch,cell⟩ := backed
  exact ⟨generation,id,value,origin.append suffix,epoch,cell⟩

theorem Resident.append (resident : Resident history ledger w)
    (suffix : List CausalJournal.Event) : Resident (history ++ suffix) ledger w :=
  fun ticket position ordinal member => (resident ticket position ordinal member).append suffix

theorem Backed.views (backed : Backed history position ordinal w)
    (epoch : Packets.epoch v = Packets.epoch w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) : Backed history position ordinal v := by
  obtain ⟨generation,id,value,origin,time,cell⟩ := backed
  exact ⟨generation,id,value,origin,epoch.trans time,congrFun cells id |>.trans cell⟩

/-- The completed allocator supplies physical backing at every actual returned
ordinal. Its native totality and before-Stop receipt timing are separate facts. -/
theorem allocated (history : List CausalJournal.Event) (packets : List DataPacket)
    (run : WGRunWitness (List SkbId)) (valid : run.Valid (packets.mapM newTxSkb))
    (device : run.before.dev = some d) (payload : packets[ordinal]? = some packet) :
    Backed (history ++ [.old (.allocated packets run)]) history.length ordinal run.after := by
  obtain ⟨id,cellAt,cell⟩ := PacketAllocation.records packets device valid ordinal packet payload
  obtain ⟨_,_,after,afterDevice,_,epoch,_⟩ := TxDisposition.ItemSeparation.allocate_result packets device valid
  have generation : Packets.epoch run.after = some d.ifindex := by
    simp [Packets.epoch,afterDevice,epoch]
  refine ⟨d.ifindex,id,PacketMaterial.material packet,?_,generation,?_⟩
  · exact ⟨packets,run,packet,by simp,valid,generation,payload,cellAt,rfl⟩
  · simp only [PacketMaterial.view,cell,Option.map_some]

/-- Actual resident boundedness, rather than an arbitrary ID-separation
assumption, keeps every old pending allocation backed after a new batch. -/
theorem Backed.allocate (backed : Backed history position ordinal w)
    (bounded : Packets.Inv w) (packets : List DataPacket)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),b)) :
    Backed history position ordinal v := by
  obtain ⟨generation,id,value,origin,epoch,cell⟩ := backed
  obtain ⟨packet,resident,material⟩ := Option.map_eq_some_iff.mp cell
  have kept := (TxDisposition.ItemSeparation.allocate_resident bounded resident run).2
  cases device : w.dev with
  | none => simp [TxDisposition.txPackets,device] at resident
  | some d =>
    obtain ⟨_,_,after,afterDevice,_,sameEpoch,_⟩ :=
      TxDisposition.ItemSeparation.allocate_result packets device run
    refine ⟨generation,id,value,origin,?_,?_⟩
    · simpa only [Packets.epoch,device,afterDevice,Option.map_some,sameEpoch] using epoch
    · simp only [PacketMaterial.view,kept,Option.map_some,material]

theorem Resident.allocate (resident : Resident history ledger w)
    (bounded : Packets.Inv w) (packets : List DataPacket)
    (run : WGRunWitness (List SkbId)) (entry : run.before = w)
    (valid : run.Valid (packets.mapM newTxSkb)) :
    Resident (history ++ [.old (.allocated packets run)]) ledger run.after := by
  intro ticket position ordinal member
  have old := resident ticket position ordinal member
  have native := valid
  rw [WGRunWitness.Valid,entry] at native
  exact (old.allocate bounded packets native).append _

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
