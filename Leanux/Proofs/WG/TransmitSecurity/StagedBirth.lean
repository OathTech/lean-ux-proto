import Leanux.Proofs.WG.TransmitSecurity.StagedOrigins

/-! Fresh journal positions and packet ordinals distinguish native packet births
from retained staged occurrences, including repeated identical payloads. -/

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal

theorem Aligned.append {related : α → β → Prop}
    (left : Aligned related xs ys) (right : Aligned related us vs) :
    Aligned related (xs ++ us) (ys ++ vs) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem Aligned.history_append (born : Aligned (Born history generation pid stamp) tickets packets)
    (suffix : List Event) : Aligned (Born (history ++ suffix) generation pid stamp) tickets packets := by
  induction born with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.append suffix) ih

theorem Aligned.position_lt (born : Aligned (Born history generation pid stamp) tickets packets)
    (member : ticket ∈ tickets) : ticket.position < history.length := by
  induction born with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact head.position_lt
    · exact ih later

def freshTickets (position first : Nat) : List Packet → List Ticket
  | [] => []
  | _ :: rest => ⟨position,first⟩ :: freshTickets position (first+1) rest

theorem freshTickets_fields (member : ticket ∈ freshTickets position first packets) :
    ticket.position = position ∧ first ≤ ticket.ordinal := by
  induction packets generalizing first with
  | nil => cases member
  | cons packet rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨rfl,Nat.le_refl _⟩
    · obtain ⟨same,bound⟩ := ih later
      exact ⟨same,by omega⟩

theorem freshTickets_unique (position first : Nat) (packets : List Packet) :
    (freshTickets position first packets).Nodup := by
  induction packets generalizing first with
  | nil => exact .nil
  | cons packet rest ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih (first+1)⟩
    intro member
    have bound := (freshTickets_fields member).2
    change first+1 ≤ first at bound
    omega

theorem freshTickets_aligned (related : Ticket → Packet → Prop) (position first : Nat)
    (packets : List Packet)
    (all : ∀ n packet, packets[n]? = some packet → related ⟨position,first+n⟩ packet) :
    Aligned related (freshTickets position first packets) packets := by
  induction packets generalizing first with
  | nil => exact .nil
  | cons packet rest ih =>
    refine .cons (by simpa using all 0 packet rfl) ?_
    apply ih
    intro n p found
    have valid := all (n+1) p found
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using valid

theorem Batch.append_births (old : Batch history generation pid stamp packets)
    (fresh : Aligned (Born (history ++ [event]) generation pid stamp)
      (freshTickets history.length 0 added) added) :
    Batch (history ++ [event]) generation pid stamp (packets ++ added) := by
  obtain ⟨tickets,unique,born⟩ := old
  refine ⟨tickets ++ freshTickets history.length 0 added,?_,
    (born.history_append [event]).append fresh⟩
  apply List.nodup_append.mpr
  refine ⟨unique,freshTickets_unique _ _ _,?_⟩
  intro first firstMember second secondMember equal
  have earlier := born.position_lt firstMember
  have atEnd := (freshTickets_fields secondMember).1
  subst second
  omega

theorem routed_births (receipt : Journal.RoutingHistory.Receipt)
    (valid : receipt.Valid) (selected : receipt.run.value = .ok pid)
    (epoch : Packets.epoch receipt.run.after = some generation)
    (peer : stagedAt receipt.run.after pid = some (stamp,staged)) (history : List Event) :
    Aligned (Born (history ++ [.old (.routed receipt.family receipt.addr receipt.packets receipt.mtu receipt.run)])
        generation pid stamp)
      (freshTickets history.length 0 (receipt.packets.map (fun p => {p with mtu := receipt.mtu})))
      (receipt.packets.map (fun p => {p with mtu := receipt.mtu})) := by
  apply freshTickets_aligned
  intro n packet payload
  simpa only [Nat.zero_add] using
    (Born.routed receipt history [] n packet staged rfl valid selected epoch peer payload)

theorem keepalive_birth (receipt : WGRunWitness Bool)
    (valid : receipt.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (ready : receipt.value = true) (epoch : Packets.epoch receipt.after = some generation)
    (empty : stagedAt receipt.before pid = some (stamp,[]))
    (peer : stagedAt receipt.after pid = some (stamp,[{mtu}]))
    (actualMtu : receipt.before.dev.map Device.mtu = some mtu) (history : List Event) :
    Batch (history ++ [.keepalivePrepared pid receipt]) generation pid stamp [{mtu}] := by
  refine ⟨[⟨history.length,0⟩],by simp, .cons ?_ .nil⟩
  exact .keepalive receipt history [] mtu rfl valid ready epoch empty peer actualMtu


end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
