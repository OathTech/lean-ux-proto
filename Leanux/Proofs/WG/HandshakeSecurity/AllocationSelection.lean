import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterialSource

/-! Each allocated packet retains its exact staging peer and selected current
key core. Conditional residency permits native release; the source certificate
does not identify peers by a numeric key slot alone. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder

def Earlier (h : List Journal.Event) (pid : PeerId) (slot : KeypairId) (core : KeyCore) : Prop :=
  ∃ pre post r peer,
    h = pre ++ Journal.Event.responder (.selected pid r) :: post ∧
    r.Valid (selectionPrefix pid) ∧ r.value = some (peer,some slot) ∧ pool r.after slot = some core

def Picked (h : List Journal.Event) (pid : PeerId) (slot : KeypairId) (w : WGWorld) : Prop :=
  ∀ core, pool w slot = some core → Earlier h pid slot core

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .allocated packets r => r.Valid (packets.mapM newTxSkb) ∧
      ∀ packet ∈ packets, Picked pre packet.peer packet.keypair r.before
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

def Keep (P : List Journal.Event → WGWorld → Prop)
    (h : List Journal.Event) (w : WGWorld) (_ : Ambient) : Prop := Safe h ∧ P h w

theorem Earlier.append (before : Earlier h pid slot core) : Earlier (h ++ suffix) pid slot core := by
  obtain ⟨pre,post,r,peer,rfl,valid,selected,resident⟩ := before
  exact ⟨pre,post ++ suffix,r,peer,by simp only [List.append_assoc,List.cons_append],valid,selected,resident⟩

theorem Picked.transport (before : Picked h pid slot w)
    (retains : Responder.Retains (pool w) (pool v)) : Picked (h ++ suffix) pid slot v := by
  intro core resident
  exact (before core (retains slot core resident)).append

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

theorem Safe.quiet_suffix (old : Safe h)
    (quiet : suffix.filterMap ReservationHistory.allocation? = []) : Safe (h ++ suffix) := by
  apply old.append
  intro pre event post position
  cases event <;> simp only [Checked]
  rename_i packets run
  have member : Journal.Event.allocated packets run ∈ suffix := by rw [position]; simp
  have found : (packets,run) ∈ suffix.filterMap ReservationHistory.allocation? := List.mem_filterMap.mpr ⟨_,member,rfl⟩
  rw [quiet] at found
  cases found

theorem empty : Safe [] := by intro pre event post position; cases pre <;> cases position

end Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
