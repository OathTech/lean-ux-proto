import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterialSource

/-! A reservation names the earlier native current-slot selection whose key
core it uses. The relation is conditional on residency and survives release;
it never infers a key lifetime from a numeric slot alone. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder

def reservation? : Journal.Event → Option (KeypairId × WGRunWitness Nat)
  | .reserved slot r => some (slot,r)
  | _ => none

def Earlier (h : List Journal.Event) (slot : KeypairId) (core : KeyCore) : Prop :=
  ∃ pre post pid r peer,
    h = pre ++ Journal.Event.responder (.selected pid r) :: post ∧
    r.value = some (peer,some slot) ∧ pool r.after slot = some core

def Picked (h : List Journal.Event) (slot : KeypairId) (w : WGWorld) : Prop :=
  ∀ core, pool w slot = some core → Earlier h slot core

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .reserved slot r => r.Valid (Nonce.reserveNative slot) ∧ Picked pre slot r.before
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

def Keep (P : List Journal.Event → WGWorld → Prop)
    (h : List Journal.Event) (w : WGWorld) (_ : Ambient) : Prop := Safe h ∧ P h w

theorem Earlier.append (before : Earlier h slot core) : Earlier (h ++ suffix) slot core := by
  obtain ⟨pre,post,pid,r,peer,rfl,selected,resident⟩ := before
  exact ⟨pre,post ++ suffix,pid,r,peer,by simp only [List.append_assoc,List.cons_append],selected,resident⟩

theorem Picked.transport (before : Picked h slot w)
    (retains : Responder.Retains (pool w) (pool v)) : Picked (h ++ suffix) slot v := by
  intro core resident
  exact (before core (retains slot core resident)).append

theorem Safe.append (old : Safe h)
    (new : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) : Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix old new

theorem Safe.quiet (old : Safe h) (quiet : reservation? event = none) : Safe (h ++ [event]) := by
  apply old.append
  intro pre e post position
  have member : e ∈ [event] := by rw [position]; simp
  have same := List.mem_singleton.mp member
  subst e
  cases event <;> simp_all only [reservation?,Checked,reduceCtorEq]

theorem Safe.quiet_suffix (old : Safe h)
    (quiet : suffix.filterMap reservation? = []) : Safe (h ++ suffix) := by
  apply old.append
  intro pre event post position
  cases event <;> simp only [Checked]
  rename_i slot run
  have member : Journal.Event.reserved slot run ∈ suffix := by rw [position]; simp
  have found : (slot,run) ∈ suffix.filterMap reservation? := List.mem_filterMap.mpr ⟨_,member,rfl⟩
  rw [quiet] at found
  cases found

theorem empty : Safe [] := by intro pre event post position; cases pre <;> cases position

end Leanux.Proofs.WG.HandshakeSecurity.ReservationSelection
