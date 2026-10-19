import Leanux.Proofs.WG.TransmitSecurity.StagedTicketIdentity

/-! Staged birth credits expire when their peer's entire saved queue is
allocated. A later allocation of another peer does not consume these credits.
This is the strengthened conservation carrier; initialization is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal Leanux.Proofs.WG.TransmitSecurity.Staged.Origins

def Uses (pid : PeerId) : Event → Prop
  | .old (.allocated packets _) => ∃ packet ∈ packets, packet.peer = pid
  | _ => False

def Available (history : List Event) (pid : PeerId) (ticket : Ticket) : Prop :=
  ∀ index event, history[index]? = some event → Uses pid event → index < ticket.position

def Quiet (pid : PeerId) (events : List Event) : Prop :=
  ∀ event ∈ events, ¬ Uses pid event

theorem Available.append (before : Available history pid ticket) (quiet : Quiet pid suffix) :
    Available (history ++ suffix) pid ticket := by
  intro index event found used
  by_cases old : index < history.length
  · exact before index event ((List.getElem?_append_left old).symm.trans found) used
  · rw [List.getElem?_append_right (by omega)] at found
    exact (quiet event (List.mem_of_getElem? found) used).elim

theorem Available.fresh (quiet : Quiet pid suffix) :
    Available (history ++ suffix) pid ⟨history.length,ordinal⟩ := by
  intro index event found used
  by_cases old : index < history.length
  · exact old
  · rw [List.getElem?_append_right (by omega)] at found
    exact (quiet event (List.mem_of_getElem? found) used).elim

def Live (history : List Event) (generation : Nat) (pid : PeerId) (stamp : Nat)
    (ticket : Ticket) (packet : Packet) : Prop :=
  Born history generation pid stamp ticket packet ∧ Available history pid ticket

def Batch (history : List Event) (generation : Nat) (pid : PeerId)
    (stamp : Nat) (packets : List Packet) : Prop :=
  ∃ tickets : List Ticket, tickets.Nodup ∧ Aligned (Live history generation pid stamp) tickets packets

theorem Aligned.forget (live : Origins.Aligned (Live history generation pid stamp) tickets packets) :
    Origins.Aligned (Born history generation pid stamp) tickets packets := by
  induction live with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.1 ih

theorem Batch.forget (batch : Batch history generation pid stamp packets) :
    Origins.Batch history generation pid stamp packets := by
  obtain ⟨tickets,unique,live⟩ := batch
  exact ⟨tickets,unique,Aligned.forget live⟩

theorem Batch.nil : Batch history generation pid stamp [] := ⟨[],by simp,.nil⟩

theorem Batch.append (before : Batch history generation pid stamp packets)
    (quiet : Quiet pid suffix) : Batch (history ++ suffix) generation pid stamp packets := by
  obtain ⟨tickets,unique,live⟩ := before
  refine ⟨tickets,unique,?_⟩
  clear unique
  induction live with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1.append suffix,head.2.append quiet⟩ ih

theorem Batch.take (before : Batch history generation pid stamp packets) (count : Nat) :
    Batch history generation pid stamp (packets.take count) := by
  obtain ⟨tickets,unique,live⟩ := before
  refine ⟨tickets.take count,unique.take,?_⟩
  clear unique
  induction count generalizing tickets packets with
  | zero => exact .nil
  | succ count ih =>
    cases live with
    | nil => exact .nil
    | cons head tail => exact .cons head (ih _ tail)

theorem Batch.drop (before : Batch history generation pid stamp packets) (count : Nat) :
    Batch history generation pid stamp (packets.drop count) := by
  obtain ⟨tickets,unique,live⟩ := before
  refine ⟨tickets.drop count,unique.drop,?_⟩
  clear unique
  induction count generalizing tickets packets with
  | zero => exact live
  | succ count ih =>
    cases live with
    | nil => exact .nil
    | cons head tail => exact ih _ tail

def Inv (history : List Event) (w : WGWorld) : Prop :=
  ∀ generation, Packets.epoch w = some generation → ∀ pid stamp packets,
    stagedAt w pid = some (stamp,packets) → Batch history generation pid stamp packets

theorem Inv.forget (before : Inv history w) : Origins.Inv history w :=
  fun generation epoch pid stamp packets resident => (before generation epoch pid stamp packets resident).forget

theorem Inv.append (before : Inv history w) (quiet : ∀ pid, Quiet pid suffix) :
    Inv (history ++ suffix) w :=
  fun generation epoch pid stamp packets resident =>
    (before generation epoch pid stamp packets resident).append (quiet pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
