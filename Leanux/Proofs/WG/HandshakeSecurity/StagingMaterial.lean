import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentHistory
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialWorkerFrames

/-! A single ordered reservation bank with native key-core evidence at packet
allocation. The bank strengthens positional credits rather than joining two
independently chosen witnesses with matching numeric slots and nonces. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder ReservationAssignments Lifetimes

def Packets (h : List Journal.Event) (packets : List DataPacket) (w : WGWorld) : Prop :=
  ∃ uses : List Use, uses.map Use.packet = packets ∧
    (uses.map Use.position).Pairwise (· < ·) ∧
    ∀ u ∈ uses, u.Valid h ∧ Available h u.position ∧
      ∀ core, pool w u.packet.keypair = some core →
        pool u.reservation.before u.packet.keypair = some core

def Checked (pre : List Journal.Event) : Journal.Event → Prop
  | .allocated packets r => r.Valid (packets.mapM newTxSkb) ∧ Packets pre packets r.before
  | _ => True

def Safe (h : List Journal.Event) : Prop :=
  ∀ pre event post, h = pre ++ event :: post → Checked pre event

def Keep (P : List Journal.Event → WGWorld → Prop)
    (h : List Journal.Event) (w : WGWorld) (_ : Ambient) : Prop := Safe h ∧ P h w

theorem Packets.forget (before : Packets h packets w) : ReservationAssignments.Packets h packets := by
  obtain ⟨uses,mapped,ordered,valid⟩ := before
  exact ⟨uses,mapped,ordered,fun u member => ⟨(valid u member).1,(valid u member).2.1⟩⟩

theorem Packets.empty : Packets h [] w :=
  ⟨[],rfl,by simp,by intro u member; cases member⟩

theorem Packets.transport (before : Packets h packets w)
    (quiet : ∀ event ∈ suffix, ReservationHistory.allocation? event = none)
    (retains : Responder.Retains (pool w) (pool v)) : Packets (h ++ suffix) packets v := by
  obtain ⟨uses,mapped,ordered,valid⟩ := before
  refine ⟨uses,mapped,ordered,?_⟩
  intro u member
  obtain ⟨entry,available,material⟩ := valid u member
  exact ⟨entry.append,available.append quiet,fun core resident => material core (retains _ core resident)⟩

theorem Packets.same_pool (before : Packets h packets w) (same : pool v = pool w) : Packets h packets v := by
  simpa only [List.append_nil] using before.transport (suffix := []) (by simp)
    (by rw [same]; exact Responder.Retains.refl _)

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
  have found : (packets,run) ∈ suffix.filterMap ReservationHistory.allocation? :=
    List.mem_filterMap.mpr ⟨_,member,rfl⟩
  rw [quiet] at found
  cases found

theorem empty : Safe [] := by intro pre event post position; cases pre <;> cases position

theorem quiet {g : WGPrefix Journal.Event α} {native : WG.M α}
    (appends : StateAppends g) (quiet : StateHistoryFrame ReservationHistory.allocation? g)
    (erases : ErasesStatePrefix g native) (frame : CoreRetains native)
    (transport : ∀ h suffix w v, (∀ event ∈ suffix, ReservationHistory.allocation? event = none) →
      Responder.Retains (pool w) (pool v) → P h w → P (h ++ suffix) v) :
    StatePrefixPreserves (Keep P) Safe g := by
  intro w a h hi
  obtain ⟨suffix,equal⟩ := appends w a h
  have excluded : suffix.filterMap ReservationHistory.allocation? = [] := by
    have same := quiet w a h
    rw [equal,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap ReservationHistory.allocation? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix (g.run w) a h).2 := by rw [equal]; exact hi.1.quiet_suffix excluded
  refine ⟨suffix,equal,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    have original := (erases w a h).symm.trans run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b original
    refine ⟨safe,?_⟩
    rw [equal]
    apply transport h suffix w v _ same hi.2
    intro event member
    cases found : ReservationHistory.allocation? event with
    | none => rfl
    | some allocation =>
      have included := List.mem_filterMap.mpr ⟨event,member,found⟩
      rw [excluded] at included
      cases included

theorem lift (action : WG.M α) (frame : CoreRetains action) :
    StatePrefixPreserves (Keep (fun h w => Packets h packets w)) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w a result v b hi run
  have retained := hi.2.transport (suffix := []) (by simp)
    ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run)
  exact ⟨hi.1,by simpa only [List.append_nil] using retained⟩

end Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
