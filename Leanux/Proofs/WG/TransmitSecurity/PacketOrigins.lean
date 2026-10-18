import Leanux.Proofs.WG.TransmitSecurity.PacketAllocation
import Leanux.Proofs.WG.TransmitSecurity.PacketMaterialFrames
import Leanux.Proofs.WG.TransmitSecurity.JournalSource

/-! Allocation provenance of resident TX material. The device epoch is part
of the identity: a reused numeric packet ID after recreation is not an old
packet. This carrier does not yet assert reservation or routing provenance. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition
variable {id : Nat}

def epoch (w : WGWorld) : Option Nat := w.dev.map (·.ifindex)

def Certificate (h : List Journal.Event) (generation id : Nat) (value : DataPacket) : Prop :=
  ∃ (packets : List DataPacket) (run : WGRunWitness (List SkbId)),
    Journal.Event.allocated packets run ∈ h ∧ run.Valid (packets.mapM newTxSkb) ∧
    epoch run.after = some generation ∧
    ∃ (n : Nat) (packet : DataPacket), packets[n]? = some packet ∧
      run.value[n]? = some id ∧ PacketMaterial.material packet = value

def Inv (h : List Journal.Event) (w : WGWorld) : Prop :=
  ∀ generation, epoch w = some generation → ∀ id packet,
    txPackets w id = some packet → Certificate h generation id (PacketMaterial.material packet)

theorem Certificate.mono (h : Certificate history generation id value)
    (included : history ⊆ later) : Certificate later generation id value := by
  obtain ⟨packets,run,member,valid,atEpoch,rest⟩ := h
  exact ⟨packets,run,included member,valid,atEpoch,rest⟩

theorem Inv.mono (h : Inv history w) (included : history ⊆ later) : Inv later w :=
  fun generation atEpoch id packet resident => (h generation atEpoch id packet resident).mono included

theorem initial (net bare : Bool) : Inv [] (Runner.initialWG net bare) := by
  intro generation atEpoch id packet resident
  cases net <;> cases bare <;> simp [txPackets,Runner.initialWG] at resident

/-- Every final resident cell is either an unchanged old cell or exactly one
of the supplied allocation values at the corresponding returned list index. -/
theorem allocation_origin (packets : List DataPacket) {w v : WGWorld} {d : Device}
    {a b : Ambient} {item : List SkbId} (device : w.dev = some d)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),b)) :
    ∀ id packet, txPackets v id = some packet →
      txPackets w id = some packet ∨
      ∃ n : Nat, packets[n]? = some packet ∧ item[n]? = some id := by
  induction packets generalizing w v d a b item with
  | nil =>
    simp only [List.mapM_nil] at run
    cases run
    exact fun _ _ resident => Or.inl resident
  | cons packet packets ih =>
    simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨id,u,clock,head,tail⟩ := run
    rw [Packets.newTxSkb_run w a d packet device] at head
    cases head
    obtain ⟨ids,last,lastClock,rest,finish⟩ := tail
    cases finish
    let next := {d with txSkbs := d.txSkbs.insert d.nextSkb packet, nextSkb := d.nextSkb + 1}
    have hd : (Packets.update w (fun v => {v with txSkbs := v.txSkbs.insert d.nextSkb packet, nextSkb := d.nextSkb + 1})).dev = some next := by simp [Packets.update,device,next]
    intro target found resident
    rcases ih hd rest target found resident with old | fresh
    · by_cases same : d.nextSkb = target
      · subst target
        have eq : packet = found := by simpa [txPackets,Packets.update,device] using old
        subst found
        exact Or.inr ⟨0,rfl,rfl⟩
      · exact Or.inl (by simpa [txPackets,Packets.update,device,Std.TreeMap.getElem?_insert,same] using old)
    · obtain ⟨n,atPacket,atItem⟩ := fresh
      exact Or.inr ⟨n+1,by simpa using atPacket,by simpa using atItem⟩

/-- A completed actual batch allocation establishes provenance for every
new cell while retaining old certificates. No queue or key-owner premise is
used; those are independent of the exact value returned by the allocator. -/
theorem allocated (packets : List DataPacket) (r : WGRunWitness (List SkbId))
    (valid : r.Valid (packets.mapM newTxSkb)) (before : Inv h r.before) :
    Inv (h ++ [.allocated packets r]) r.after := by
  rcases r with ⟨item,w,v,a,b⟩
  change ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),b) at valid
  intro generation atEpoch id packet resident
  cases device : w.dev with
  | none =>
    cases packets with
    | nil => cases valid; simp [txPackets,device] at resident
    | cons p ps =>
      simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at valid
      obtain ⟨_,_,_,first,_⟩ := valid
      simp [newTxSkb,liftSkb_run,device] at first
  | some d =>
    obtain ⟨_,_,e,afterDevice,_,epochEq,_⟩ := ItemSeparation.allocate_result packets device valid
    have beforeEpoch : epoch w = some generation := by
      simpa [epoch,device,afterDevice,epochEq] using atEpoch
    rcases allocation_origin packets device valid id packet resident with old | fresh
    · exact (before generation beforeEpoch id packet old).mono (by intro x hx; exact List.mem_append_left _ hx)
    · obtain ⟨n,atPacket,atItem⟩ := fresh
      exact ⟨packets,⟨item,w,v,a,b⟩,by simp,valid,atEpoch,n,packet,atPacket,atItem,rfl⟩

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
