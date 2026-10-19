import Leanux.Proofs.WG.TransmitSecurity.StagedBirth

/-! Birth tickets decode from their actual final-journal position. Equal
payloads do not identify tickets, and a ticket cannot change its peer or epoch. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects.CausalJournal

def describe (history : List Event) (ticket : Ticket) : Option (Nat × PeerId × Nat × Packet) := do
  let event ← history[ticket.position]?
  match event with
  | .old (.routed _ _ packets mtu run) =>
    let .ok pid := run.value | none
    let generation ← Packets.epoch run.after
    let (stamp,_) ← stagedAt run.after pid
    let packet ← (packets.map (fun p => {p with mtu}))[ticket.ordinal]?
    pure (generation,pid,stamp,packet)
  | .keepalivePrepared pid run =>
    if ticket.ordinal != 0 then none else do
      let generation ← Packets.epoch run.after
      let (stamp,_) ← stagedAt run.after pid
      let mtu ← run.before.dev.map Device.mtu
      pure (generation,pid,stamp,{mtu})
  | _ => none

theorem Born.describe (born : Born history generation pid stamp ticket packet) :
    describe history ticket = some (generation,pid,stamp,packet) := by
  cases born with
  | routed receipt pre post ordinal packet staged position valid selected epoch peer payload =>
    simp only [List.getElem?_map] at payload
    simp [Staged.Origins.describe,position,selected,epoch,peer,payload]
  | keepalive receipt pre post mtu position valid ready epoch empty peer actualMtu =>
    simp [Staged.Origins.describe,position,epoch,peer,actualMtu]

/-- One actual birth position and ordinal cannot authorize different packet
peers, device epochs, peer allocations or plaintexts. Repeated use of the same
ticket is a separate conservation question. -/
theorem Born.unique (first : Born history generation pid stamp ticket packet)
    (second : Born history otherGeneration otherPid otherStamp ticket otherPacket) :
    generation = otherGeneration ∧ pid = otherPid ∧ stamp = otherStamp ∧ packet = otherPacket := by
  have same := Option.some.inj (first.describe.symm.trans second.describe)
  simpa only [Prod.mk.injEq] using same

theorem Aligned.ticket_member (aligned : Aligned (Born history generation pid stamp) tickets packets)
    (member : ticket ∈ tickets) : ∃ packet, Born history generation pid stamp ticket packet := by
  induction aligned with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst ticket
      exact ⟨_,head⟩
    · exact ih inside

theorem Aligned.distinct_peers_disjoint
    (first : Aligned (Born history generation pid stamp) tickets packets)
    (second : Aligned (Born history otherGeneration otherPid otherStamp) otherTickets otherPackets)
    (different : pid ≠ otherPid) : ∀ ticket, ticket ∈ tickets → ticket ∈ otherTickets → False := by
  intro ticket inFirst inSecond
  obtain ⟨packet,firstBorn⟩ := first.ticket_member inFirst
  obtain ⟨otherPacket,secondBorn⟩ := second.ticket_member inSecond
  exact different (firstBorn.unique secondBorn).2.1

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
