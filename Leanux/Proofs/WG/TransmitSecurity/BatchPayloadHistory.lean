import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalSessionSource
import Leanux.Proofs.WG.TransmitSecurity.BatchHistory
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverCutFrames

/-! Actual allocation batches retain exactly the plaintext sequence from their
native staged selection. Packet positions, including duplicate byte strings,
are retained; this is the staging-to-allocation part of TX conservation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchPayload
open Leanux Leanux.WG Leanux.Proofs.Logged

def Selected (h : List Journal.Event) (pid : PeerId) (peer : Peer) (slot : KeypairId) : Prop :=
  ∃ r : WGRunWitness (Option (Peer × Option KeypairId)),
    Journal.Event.responder (.selected pid r) ∈ h ∧
    r.Valid (HandshakeSecurity.Responder.selectionPrefix pid) ∧ r.value = some (peer,some slot)

def Shape (pid : PeerId) (slot : KeypairId) (plain : List Packet) (packets : List DataPacket) : Prop :=
  packets.map DataPacket.plaintext = plain ∧ BatchHistory.Aligned pid slot packets

def Source (h : List Journal.Event) (packets : List DataPacket) : Prop :=
  ∃ pid peer slot, Selected h pid peer slot ∧ Shape pid slot peer.staged packets

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .allocated packets r => r.Valid (packets.mapM newTxSkb) ∧ Source pre packets
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

def Monotone (P : List Journal.Event → Prop) : Prop := ∀ h k, h ⊆ k → P h → P k

def Keep (P : List Journal.Event → Prop) (h : List Journal.Event) (_ : WGWorld) (_ : Ambient) : Prop :=
  Safe h ∧ P h

theorem Selected.mono (selected : Selected h pid peer slot) (included : h ⊆ later) :
    Selected later pid peer slot := by
  obtain ⟨r,member,valid,value⟩ := selected
  exact ⟨r,included member,valid,value⟩

theorem Source.mono (source : Source h packets) (included : h ⊆ later) : Source later packets := by
  obtain ⟨pid,peer,slot,selected,shape⟩ := source
  exact ⟨pid,peer,slot,selected.mono included,shape⟩

theorem Safe.append (old : Safe h)
    (new : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) : Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix old new

theorem Safe.quiet (old : Safe h) (quiet : ReservationHistory.allocation? event = none) : Safe (h ++ [event]) := by
  apply old.append
  intro pre e post position
  have member : e ∈ [event] := by rw [position]; simp
  have same := List.mem_singleton.mp member
  subst e
  cases event <;> simp_all only [ReservationHistory.allocation?,Checked,reduceCtorEq]

theorem Safe.quiet_suffix (old : Safe h) (quiet : suffix.filterMap ReservationHistory.allocation? = []) : Safe (h ++ suffix) := by
  apply old.append
  intro pre event post position
  cases event <;> simp only [Checked]
  rename_i packets run
  have member : Journal.Event.allocated packets run ∈ suffix := by rw [position]; simp
  have found : (packets,run) ∈ suffix.filterMap ReservationHistory.allocation? := List.mem_filterMap.mpr ⟨_,member,rfl⟩
  rw [quiet] at found
  cases found

theorem empty : Safe [] := by intro pre event post position; cases pre <;> cases position

end Leanux.Proofs.WG.TransmitSecurity.BatchPayload
