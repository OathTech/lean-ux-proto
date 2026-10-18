import Leanux.Proofs.WG.AuthenticatedEffects.TimerSelection
import Leanux.Proofs.Logged.ProjectsUnder

/-! A single scope for the shared driver's actual selected timer suffix.
It records the saved device and live product state before validation, deletion
and callback. The body and its failure-retaining journal remain continuous. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerDispatch
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Selection where
  saved : Device
  bound : UInt64
  peer : PeerId
  timer : PeerTimer
  entry : WheelEntry
  before : World

def Selection.Valid (r : Selection) : Prop :=
  r.before.wg.dev = some r.saved ∧
    TimerWheel.nextDue r.saved r.bound = some (r.peer,r.timer,r.entry)

def Selection.Cause (h : List TimerRoot.Event) (r : Selection) : Prop :=
  ∃ stamp expires,
    TimerSlots.Pending r.before.wg r.peer r.timer stamp expires r.entry ∧
    TimerSlots.HasCause h r.peer r.timer stamp expires r.entry

/-- The native caller supplies the saved device and successful nextDue result.
Reading the observer's input state is a proof-side observation, not a new native
getter. The native validation/deletion/callback suffix is executed exactly once. -/
def scope (record : Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (entry : WheelEntry) (body : PrefixM E α) : PrefixM E α :=
  fun w => (do emitPrefix (record ⟨d,j,pid,t,entry,w⟩); body).run w

theorem scope_run (record : Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (entry : WheelEntry) (body : PrefixM E α) (w : World) (h : List E) :
    runPrefix (scope record d j pid t entry body) w h =
      runPrefix body w (h ++ [record ⟨d,j,pid,t,entry,w⟩]) := by
  change runPrefix (do emitPrefix (record ⟨d,j,pid,t,entry,w⟩); body) w h = _
  simp only [runPrefix_bind,runPrefix_emit]

theorem scope_erases (record : Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (entry : WheelEntry) {body : PrefixM E α} {native : Leanux.M α}
    (erases : ErasesPrefix body native) : ErasesPrefix (scope record d j pid t entry body) native := by
  intro w h
  rw [scope_run]
  exact erases w _

theorem scope_projects (record : Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (entry : WheelEntry) (decode : E → Option F)
    (invisible : ∀ r, decode (record r) = none)
    {body : PrefixM E α} {target : PrefixM F β} (value : α → β)
    (projects : ProjectsPrefix decode value body target) :
    ProjectsPrefix decode value (scope record d j pid t entry body) target := by
  intro w h
  rw [scope_run]
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
    invisible,Option.toList_none,List.nil_append,List.append_nil] using projects w (h ++ [record ⟨d,j,pid,t,entry,w⟩])

theorem scope_appends (record : Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (entry : WheelEntry) {body : PrefixM E α} (appends : Appends body) :
    Appends (scope record d j pid t entry body) := by
  intro w h
  obtain ⟨suffix,history⟩ := appends w (h ++ [record ⟨d,j,pid,t,entry,w⟩])
  refine ⟨record ⟨d,j,pid,t,entry,w⟩ :: suffix,?_⟩
  rw [scope_run,history]
  simp only [List.append_assoc,List.singleton_append]

theorem selection_cause (r : Selection) (valid : r.Valid)
    (carrier : TimerSlots.Carrier h r.before.wg) : r.Cause h := by
  obtain ⟨p,resident,wheel⟩ := TimerSlots.due_resident r.saved r.bound r.peer r.timer r.entry
    (TimerSlots.nextDue_member r.saved r.bound r.peer r.timer r.entry valid.2)
  have pending : TimerSlots.Pending r.before.wg r.peer r.timer p.internalId (p.timer r.timer) r.entry := by
    simp [TimerSlots.Pending,TimerSlots.view,valid.1,resident,wheel]
  exact ⟨p.internalId,p.timer r.timer,pending,carrier _ _ _ _ _ pending⟩

/-- The first event remains at its exact incoming journal position, including
when validation or the callback Stops. The body need only append events. -/
theorem scope_entry (record : Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (entry : WheelEntry) {body : PrefixM E α} (appends : Appends body)
    (w : World) (h : List E) :
    ∃ suffix, (runPrefix (scope record d j pid t entry body) w h).2 =
      h ++ record ⟨d,j,pid,t,entry,w⟩ :: suffix := by
  obtain ⟨suffix,history⟩ := appends w (h ++ [record ⟨d,j,pid,t,entry,w⟩])
  exact ⟨suffix,by rw [scope_run,history]; simp only [List.append_assoc,List.singleton_append]⟩

theorem scope_entry_cause (record : Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (t : PeerTimer) (entry : WheelEntry) {body : PrefixM E α} (appends : Appends body)
    (w : World) (h : List E) (roots : List TimerRoot.Event)
    (saved : w.wg.dev = some d) (selected : TimerWheel.nextDue d j = some (pid,t,entry))
    (carrier : TimerSlots.Carrier roots w.wg) :
    ∃ suffix, (runPrefix (scope record d j pid t entry body) w h).2 =
      h ++ record ⟨d,j,pid,t,entry,w⟩ :: suffix ∧
      Selection.Valid ⟨d,j,pid,t,entry,w⟩ ∧ Selection.Cause roots ⟨d,j,pid,t,entry,w⟩ := by
  obtain ⟨suffix,history⟩ := scope_entry record d j pid t entry appends w h
  exact ⟨suffix,history,⟨saved,selected⟩,selection_cause _ ⟨saved,selected⟩ carrier⟩

end Leanux.Proofs.WG.AuthenticatedEffects.TimerDispatch
