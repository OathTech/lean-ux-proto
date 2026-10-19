import Leanux.Proofs.WG.TransmitSecurity.StagedKeepaliveFinal
import Leanux.Proofs.WG.TransmitSecurity.StagedAdmission

/-! Staged plaintext origins retain the actual birth position, packet ordinal,
device epoch and peer allocation. Equal payloads are distinct occurrences.
These predicates are a carrier, not an initialized claim by themselves. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Queues
open AuthenticatedEffects.CausalJournal

structure Ticket where
  position : Nat
  ordinal : Nat
  deriving DecidableEq

inductive Born (history : List Event) (generation : Nat) (pid : PeerId)
    (stamp : Nat) : Ticket → Packet → Prop where
  | routed (receipt : Journal.RoutingHistory.Receipt) (pre post : List Event)
      (ordinal : Nat) (packet : Packet) (staged : List Packet)
      (position : history = pre ++ .old (.routed receipt.family receipt.addr
        receipt.packets receipt.mtu receipt.run) :: post)
      (valid : receipt.Valid) (selected : receipt.run.value = .ok pid)
      (epoch : Packets.epoch receipt.run.after = some generation)
      (peer : stagedAt receipt.run.after pid = some (stamp,staged))
      (payload : (receipt.packets.map (fun p => {p with mtu := receipt.mtu}))[ordinal]? = some packet) :
      Born history generation pid stamp ⟨pre.length,ordinal⟩ packet
  | keepalive (receipt : WGRunWitness Bool) (pre post : List Event) (mtu : Nat)
      (position : history = pre ++ .keepalivePrepared pid receipt :: post)
      (valid : receipt.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
      (ready : receipt.value = true)
      (epoch : Packets.epoch receipt.after = some generation)
      (empty : stagedAt receipt.before pid = some (stamp,[]))
      (peer : stagedAt receipt.after pid = some (stamp,[{mtu}]))
      (actualMtu : receipt.before.dev.map Device.mtu = some mtu) :
      Born history generation pid stamp ⟨pre.length,0⟩ {mtu}

theorem Born.position_lt (born : Born history generation pid stamp ticket packet) :
    ticket.position < history.length := by
  cases born with
  | routed receipt pre post ordinal packet staged position =>
    rw [position]
    simp
  | keepalive receipt pre post mtu position =>
    rw [position]
    simp

theorem Born.append (born : Born history generation pid stamp ticket packet)
    (suffix : List Event) : Born (history ++ suffix) generation pid stamp ticket packet := by
  cases born with
  | routed receipt pre post ordinal packet staged position valid selected epoch peer payload =>
    exact .routed receipt pre (post ++ suffix) ordinal packet staged
      (by rw [position]; simp only [List.append_assoc,List.cons_append]) valid selected epoch peer payload
  | keepalive receipt pre post mtu position valid ready epoch empty peer actualMtu =>
    exact .keepalive receipt pre (post ++ suffix) mtu
      (by rw [position]; simp only [List.append_assoc,List.cons_append]) valid ready epoch empty peer actualMtu

inductive Aligned (related : α → β → Prop) : List α → List β → Prop where
  | nil : Aligned related [] []
  | cons : related a b → Aligned related xs ys → Aligned related (a :: xs) (b :: ys)

def Batch (history : List Event) (generation : Nat) (pid : PeerId)
    (stamp : Nat) (packets : List Packet) : Prop :=
  ∃ tickets : List Ticket, tickets.Nodup ∧ Aligned (Born history generation pid stamp) tickets packets

theorem Batch.nil : Batch history generation pid stamp [] := ⟨[],by simp,.nil⟩

theorem Batch.append_history (batch : Batch history generation pid stamp packets)
    (suffix : List Event) : Batch (history ++ suffix) generation pid stamp packets := by
  obtain ⟨tickets,unique,born⟩ := batch
  refine ⟨tickets,unique,?_⟩
  clear unique
  induction born with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.append suffix) ih

theorem Batch.take (batch : Batch history generation pid stamp packets) (count : Nat) :
    Batch history generation pid stamp (packets.take count) := by
  obtain ⟨tickets,unique,born⟩ := batch
  refine ⟨tickets.take count,unique.take,?_⟩
  clear unique
  induction count generalizing tickets packets with
  | zero => exact .nil
  | succ count ih =>
    cases born with
    | nil => exact .nil
    | cons head tail => exact .cons head (ih _ tail)

theorem Batch.drop (batch : Batch history generation pid stamp packets) (count : Nat) :
    Batch history generation pid stamp (packets.drop count) := by
  obtain ⟨tickets,unique,born⟩ := batch
  refine ⟨tickets.drop count,unique.drop,?_⟩
  clear unique
  induction count generalizing tickets packets with
  | zero => exact born
  | succ count ih =>
    cases born with
    | nil => exact .nil
    | cons head tail => exact ih _ tail

def Inv (history : List Event) (w : WGWorld) : Prop :=
  ∀ generation, Packets.epoch w = some generation → ∀ pid stamp packets,
    stagedAt w pid = some (stamp,packets) → Batch history generation pid stamp packets

theorem Inv.append (before : Inv history w) (suffix : List Event) : Inv (history ++ suffix) w :=
  fun generation epoch pid stamp packets resident =>
    (before generation epoch pid stamp packets resident).append_history suffix


def Checked (pre : List Event) : Event → Prop
  | .old (.responder (.selected pid run)) =>
    ∀ peer key, run.value = some (peer,key) →
      ∃ generation, Packets.epoch run.before = some generation ∧
        Batch pre generation pid peer.internalId peer.staged
  | _ => True

def Safe (history : List Event) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked pre event

def Carrier (history : List Event) (w : WGWorld) : Prop := Inv history w ∧ Safe history

theorem Safe.empty : Safe [] := by
  intro pre event post position
  have lengths := congrArg List.length position
  simp at lengths

theorem Safe.append (before : Safe history)
    (checked : ∀ pre event post, suffix = pre ++ event :: post → Checked (history ++ pre) event) :
    Safe (history ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked history suffix before checked

theorem Safe.emit (before : Safe history) (checked : Checked history event) :
    Safe (history ++ [event]) := by
  apply before.append
  intro pre entry post position
  cases pre with
  | nil => cases position; simpa only [List.append_nil] using checked
  | cons head tail =>
    have lengths := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

def Quiet : Event → Prop
  | .old (.responder (.selected _ _)) => False
  | _ => True

theorem checked_quiet (event : Event) (quiet : Quiet event) (pre : List Event) :
    Checked pre event := by
  cases event with
  | old event =>
    cases event with
    | responder event => cases event <;> first | exact quiet.elim | trivial
    | _ => trivial
  | _ => trivial

theorem Safe.quiet (before : Safe history) (quiet : ∀ event ∈ suffix, Quiet event) :
    Safe (history ++ suffix) := by
  apply before.append
  intro pre event post position
  apply checked_quiet event
  apply quiet event
  rw [position]
  simp

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
