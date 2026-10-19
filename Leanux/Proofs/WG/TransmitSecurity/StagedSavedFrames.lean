import Leanux.Proofs.WG.TransmitSecurity.StagedRestoreOrigins

/-! Saved source positions survive exact native queue frames and new unrelated journal entries. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal

theorem Saved.views (saved : Saved h pid peer w)
    (epoch : Packets.epoch v = Packets.epoch w) (queues : stagedAt v = stagedAt w) :
    Saved h pid peer v := by
  obtain ⟨generation,atEpoch,empty,batch⟩ := saved
  exact ⟨generation,epoch.trans atEpoch,by rw [queues]; exact empty,batch⟩

def Held (pid : PeerId) (peer : Peer) (history : List Event) (w : WGWorld) (_ : Ambient) : Prop :=
  Carrier history w ∧ Saved history pid peer w

theorem StateSafe.saved (safe : StateSafe action) (erase : ErasesStatePrefix action native)
    (epoch : SameView Packets.epoch native) (queues : SameView stagedAt native) :
    StatePrefixPreserves (Held pid peer) Safe action := by
  intro w a h before
  obtain ⟨suffix,position,history,after⟩ := safe w a h before.1
  refine ⟨suffix,position,history,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erase w a h).symm.trans outcome
    have saved := before.2.views
      ((ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
      ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a value v b run)
    refine ⟨by simpa only [outcome] using after,?_⟩
    rw [position]
    exact saved.append suffix

def selection? : Event → Option Unit
  | .old (.responder (.selected _ _)) => some ()
  | _ => none

theorem quiet_iff (event : Event) : Quiet event ↔ selection? event = none := by
  cases event with
  | old event =>
    cases event with
    | responder event => cases event <;> simp [Quiet,selection?]
    | _ => simp [Quiet,selection?]
  | _ => simp [Quiet,selection?]

theorem state_quiet {action : WGPrefix Event α} {native : WG.M α}
    (appends : StateAppends action) (quiet : StateHistoryFrame selection? action)
    (erase : ErasesStatePrefix action native) (kept : ∀ h, Preserves (Inv h) native) :
    StateSafe action := by
  intro w a h before
  obtain ⟨suffix,position⟩ := appends w a h
  have noSelection : suffix.filterMap selection? = [] := by
    have frame := quiet w a h
    rw [position,List.filterMap_append] at frame
    have sizes := congrArg List.length frame
    cases found : suffix.filterMap selection? with
    | nil => rfl
    | cons x xs => simp only [List.length_append,found,List.length_cons] at sizes; omega
  have safe : Safe (runPrefix (action.run w) a h).2 := by
    rw [position]
    apply before.2.quiet
    intro event member
    apply (quiet_iff event).mpr
    cases found : selection? event with
    | none => rfl
    | some value =>
      have present := List.mem_filterMap.mpr ⟨event,member,found⟩
      rw [noSelection] at present
      cases present
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have run : (native.run w).run a = .ok ((value,v),b) := (erase w a h).symm.trans outcome
    have inv := (hoare_iff_run_ambient _ _ _).mp (kept h) w a value v b before.1 run
    refine ⟨?_,safe⟩
    rw [position]
    exact inv.append suffix

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins

