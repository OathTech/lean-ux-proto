import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityBank

/-! The allocation history carries one live-ticket assignment per actual
batch. This interface keeps its native initialization obligation explicit. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal Leanux.Proofs.WG.TransmitSecurity.Staged.Origins

variable {index : Nat} {packets : List DataPacket} {r : WGRunWitness (List SkbId)}

structure Assignment where
  generation : Nat
  pid : PeerId
  stamp : Nat
  tickets : List Ticket

def Assignment.Valid (history : List Event) (packets : List DataPacket) (assignment : Assignment) : Prop :=
  assignment.tickets.Nodup ∧
    Origins.Aligned (Live history assignment.generation assignment.pid assignment.stamp)
      assignment.tickets (packets.map DataPacket.plaintext) ∧
    ∀ packet ∈ packets, packet.peer = assignment.pid

def Source (history : List Event) (packets : List DataPacket) : Prop :=
  ∃ assignment : Assignment, assignment.Valid history packets

def Checked (pre : List Event) : Event → Prop
  | .old (.allocated packets r) => r.Valid (packets.mapM newTxSkb) ∧ Source pre packets
  | _ => True

def Safe (history : List Event) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked pre event

def Carrier (history : List Event) (w : WGWorld) : Prop := Inv history w ∧ Safe history

def allocation? : Event → Option (List DataPacket × WGRunWitness (List SkbId))
  | .old (.allocated packets r) => some (packets,r)
  | _ => none

theorem no_use (quiet : allocation? event = none) : ¬ Uses pid event := by
  cases event with
  | old event => cases event <;> simp_all only [allocation?,Uses,reduceCtorEq,not_false_eq_true]
  | _ => simp only [Uses,not_false_eq_true]

theorem quiet_event (quiet : allocation? event = none) : Checked pre event := by
  cases event with
  | old event => cases event <;> simp_all only [allocation?,Checked,reduceCtorEq]
  | _ => trivial

theorem Safe.empty : Safe [] := by
  intro pre event post position
  cases pre <;> cases position

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

theorem Safe.quiet (before : Safe history)
    (quiet : ∀ event ∈ suffix, allocation? event = none) : Safe (history ++ suffix) := by
  apply before.append
  intro pre event post position
  apply quiet_event
  apply quiet event
  rw [position]
  simp

theorem Source.of_batch (batch : Batch history generation pid stamp (packets.map DataPacket.plaintext))
    (owner : ∀ packet ∈ packets, packet.peer = pid) : Source history packets := by
  obtain ⟨tickets,unique,live⟩ := batch
  exact ⟨⟨generation,pid,stamp,tickets⟩,unique,live,owner⟩

theorem Safe.at (safe : Safe history)
    (found : history[index]? = some (.old (.allocated packets r))) :
    r.Valid (packets.mapM newTxSkb) ∧ Source (history.take index) packets := by
  obtain ⟨bound,value⟩ := List.getElem?_eq_some_iff.mp found
  apply safe (history.take index) (.old (.allocated packets r)) (history.drop (index+1))
  rw [←value,List.getElem_cons_drop bound,List.take_append_drop]

noncomputable def bank (history : List Event) : Bank := by
  classical
  exact fun index => match history[index]? with
    | some (.old (.allocated packets _)) =>
        if claim : Source (history.take index) packets then claim.choose.tickets else []
    | _ => []

theorem bank_valid (safe : Safe history) : BankValid history (bank history) := by
  intro index packets r found
  have source := (safe.at found).2
  have witness := source.choose_spec
  simp only [bank,found,source,↓reduceDIte]
  exact ⟨witness.1,source.choose.generation,source.choose.pid,source.choose.stamp,witness.2⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
