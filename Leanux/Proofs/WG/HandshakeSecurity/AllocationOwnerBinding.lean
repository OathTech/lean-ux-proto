import Leanux.Proofs.WG.HandshakeSecurity.AllocationSelectionBinding

/-! Historical peer ownership for actual AEAD material. The nonnull owner is
read from the key resident at the packet's actual allocation entry, after
native staging's successful owner dereference. Retirement may subsequently
clear the owner word; the allocation stamp and sending material still bind
the historical key to the later actual cipher call. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.AllocationOwner
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder Lifetimes Queues

def Historical (h : List Journal.Event) (r : WorkerEncryption.Receipt) : Prop :=
  ∃ (packets : List DataPacket) (allocation : WGRunWitness (List SkbId))
    (index : Nat) (input : DataPacket) (device : Device) (key : Keypair),
    Journal.Event.allocated packets allocation ∈ h ∧
    allocation.Valid (packets.mapM newTxSkb) ∧
    packets[index]? = some input ∧ allocation.value[index]? = some r.id ∧
    PacketMaterial.material input = PacketMaterial.material r.read.value ∧
    allocation.before.dev = some device ∧ device.keypairs[input.keypair]? = some key ∧
    key.peer = some r.read.value.peer ∧ keyCore key = keyCore r.cipher.keyRead.value

theorem Historical.mono (owned : Historical h r) (included : h ⊆ later) : Historical later r := by
  obtain ⟨packets,allocation,index,input,device,key,member,rest⟩ := owned
  exact ⟨packets,allocation,index,input,device,key,included member,rest⟩

theorem Historical.append (owned : Historical h r) : Historical (h ++ suffix) r :=
  owned.mono (by intro e member; exact List.mem_append_left _ member)

theorem historical_of_binding (bound : ResidentMaterial.BoundReceipt h r) : Historical h r := by
  obtain ⟨generation,_,packets,allocation,index,input,member,valid,_,atInput,atId,material,resident,owner⟩ := bound
  obtain ⟨key,atKey,core⟩ := Option.map_eq_some_iff.mp resident
  obtain ⟨device,atDevice,stored⟩ := Option.bind_eq_some_iff.mp atKey
  have peer : input.peer = r.read.value.peer := by
    simpa only [PacketMaterial.material] using congrArg DataPacket.peer material
  have word : key.peer = some input.peer := by
    simpa only [RxCredits.keyWords,atDevice,Option.bind_some,stored,Option.map_some,Option.some.injEq] using owner
  exact ⟨packets,allocation,index,input,device,key,member,valid,atInput,atId,material,
    atDevice,stored,peer ▸ word,core⟩

/-- Every actual initialized AEAD has an earlier allocation-entry key whose
nonnull owner is the packet's peer, with the same allocation stamp and sending
material as the cipher read. The same peer selected that key as current. -/
theorem initialized_encryption (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
      pre ++ .encrypted r :: post) :
    r.Valid ∧ Historical pre r ∧
      AllocationSelection.Earlier pre r.read.value.peer r.read.value.keypair
        (keyCore r.cipher.keyRead.value) := by
  obtain ⟨valid,binding⟩ := ResidentMaterial.initialized trace placeholders pre (.encrypted r) post position
  have member : r ∈ ((runPrefixOuter (Journal.execute trace placeholders) []).2).filterMap Journal.encryption? := by
    rw [position]
    exact List.mem_filterMap.mpr ⟨.encrypted r,by simp,rfl⟩
  have batch := (BatchJournal.Scheduler.initialized trace placeholders r member).2.2
  have selected := AllocationSelection.initialized trace placeholders
  rw [position] at selected
  exact ⟨valid,historical_of_binding (binding batch),
    AllocationSelection.selected_of_binding selected.prefix (binding batch)⟩

/-- The final causal observer carries the same earlier packet allocation and
current selection. This exact event projection covers occurrences preceding
an internal Stop, without an incoming state or C2 hypothesis. -/
theorem final_encryption (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?) = pre ++ .encrypted r :: post) :
    r.Valid ∧ Historical pre r ∧
      AllocationSelection.Earlier pre r.read.value.peer r.read.value.keypair
        (keyCore r.cipher.keyRead.value) := by
  have history := congrArg Prod.snd (AuthenticatedEffects.CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at history
  exact initialized_encryption trace placeholders pre post r (history.trans position)

end Leanux.Proofs.WG.HandshakeSecurity.AllocationOwner
