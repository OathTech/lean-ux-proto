import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenanceFrames

/-! Fixed selected tickets are assigned to their native allocation ordinals.
The relation must be the actual birth/peer relation supplied by the held
source carrier; arbitrary alignment or equal plaintexts are insufficient. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal

theorem allocated_ticket (packets : List DataPacket) (run : WGRunWitness (List SkbId))
    (native : run.Valid (packets.mapM newTxSkb)) (device : run.before.dev = some d)
    (epoch : Packets.epoch run.before = some generation)
    (aligned : Aligned (fun ticket packet =>
      Born history generation pid stamp ticket packet.plaintext ∧ packet.peer = pid) tickets packets)
    (atTicket : tickets[ordinal]? = some ticket) :
    AllocatedBorn (history ++ [.old (.allocated packets run)]) ticket history.length ordinal := by
  have sameEpoch : d.ifindex = generation := by
    simpa only [Packets.epoch,device,Option.map_some,Option.some.injEq] using epoch
  obtain ⟨packet,id,_,related,_,origin,_,_⟩ :=
    AllocatedObligation.allocated_ticket history packets run native device aligned atTicket
  rw [sameEpoch] at origin
  refine ⟨generation,id,PacketMaterial.material packet,origin,pid,stamp,?_,?_⟩
  · exact related.1.append _
  · exact related.2

/-- This is the allocation-link counterpart of core_allocate. Each changed
ticket uses its own ordinal in the actual selected list; previous links and
terminal evidence are retained. The birth alignment remains a named premise. -/
theorem AllocationLinks.assigned (before : AllocationLinks history ledger)
    (packets : List DataPacket) (run : WGRunWitness (List SkbId))
    (native : run.Valid (packets.mapM newTxSkb)) (device : run.before.dev = some d)
    (epoch : Packets.epoch run.before = some generation)
    (aligned : Aligned (fun ticket packet =>
      Born history generation pid stamp ticket packet.plaintext ∧ packet.peer = pid)
      (pendingAt (.selected takePosition) ledger) packets) :
    AllocationLinks (history ++ [.old (.allocated packets run)])
      (assignBatch takePosition history.length ledger) := by
  intro ticket batch ordinal member
  rcases assignBatch_cases member with old | ⟨selected,rfl,rfl⟩
  · exact (before ticket batch ordinal old).append _
  · exact allocated_ticket packets run native device epoch aligned
      (ticketOrdinal_get (mem_pendingAt.mpr selected))

theorem AllocationLinks.transferred (before : AllocationLinks history ledger)
    (source target : Pending)
    (notSource : ∀ batch ordinal, Pending.allocated batch ordinal ≠ source)
    (notTarget : ∀ batch ordinal, Pending.allocated batch ordinal ≠ target) :
    AllocationLinks history (transferLocation source target ledger) := by
  intro ticket batch ordinal member
  have old := mem_pendingAt.mpr member
  rw [pendingAt_transfer_other (notSource batch ordinal) (notTarget batch ordinal)] at old
  exact before ticket batch ordinal (mem_pendingAt.mp old)

theorem AllocationLinks.admitted (before : AllocationLinks history ledger)
    (birthPosition generation pid stamp : Nat) (packets : List Packet) :
    AllocationLinks history
      (StagedAdmission.appendBirths ledger birthPosition (.staged generation pid stamp) packets) := by
  intro ticket batch ordinal member
  have old := mem_pendingAt.mpr member
  rw [StagedAdmission.pending_other (by simp)] at old
  exact before ticket batch ordinal (mem_pendingAt.mp old)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
