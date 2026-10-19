import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTickets

/-! Final peer release consumes the same incoming ordered staged tickets.
The charge and disappearance are both consequences of the actual counted
erase receipt, rather than an inference from a missing peer in a later state. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity.Staged TransmitSecurity.Staged.Origins

/-- At the native final-release cut every staged obligation is charged once
under its original peer allocation and device epoch. A later Stop is outside
this receipt and cannot erase its already completed counter update. -/
theorem native_release (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (valid : r.Valid (StagedDisposal.releaseCut peer)) (pid : PeerId) (p : Peer)
    (released : r.value = some (pid,p))
    (tickets : List Ticket) (R : Ticket → Packet → Prop)
    (aligned : Aligned R tickets p.staged) :
    peer = some pid ∧ stagedAt r.before pid = some (p.internalId,p.staged) ∧
    stagedAt r.after pid = none ∧
    (∃ count, dropped r.before = some count ∧ dropped r.after = some (count+tickets.length)) ∧
    Packets.epoch r.after = Packets.epoch r.before ∧
    (∀ q, pid ≠ q → stagedAt r.after q = stagedAt r.before q) := by
  obtain ⟨device,selected,before,resident,_,absent,charged,epoch,others⟩ :=
    StagedDisposal.release_exact peer r valid pid p released
  refine ⟨selected,?_,absent,?_,epoch,others⟩
  · simp only [stagedAt,before,Option.bind_some,resident,Option.map_some]
  · refine ⟨device.txDropped,?_,?_⟩
    · simp only [dropped,before,Option.map_some]
    · simpa only [aligned_length aligned] using charged

/-- With unique incoming identities the terminal prefix is precisely that
whole list: there is no retained suffix and no duplication within the charge. -/
theorem release_all_tickets (tickets : List Ticket) (packets : List Packet)
    (R : Ticket → Packet → Prop) (aligned : Aligned R tickets packets)
    (unique : tickets.Nodup) :
    tickets.take packets.length = tickets ∧ tickets.drop packets.length = [] ∧
    (tickets.take packets.length).Nodup := by
  have length := aligned_length aligned
  rw [← length,List.take_length,List.drop_length]
  exact ⟨rfl,rfl,unique⟩

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation
