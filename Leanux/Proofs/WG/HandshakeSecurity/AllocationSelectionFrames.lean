import Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection

/-! Allocation-free observers preserve the positional selection claim.
Native staging leaves additionally retain the selected immutable key core. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder Lifetimes

theorem product_quiet {g : PrefixM Journal.Event α} (app : Appends g)
    (frame : HistoryFrame ReservationHistory.allocation? g) : Driver.ProductHistorySafe Safe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have excluded : suffix.filterMap ReservationHistory.allocation? = [] := by
    have same := frame w h
    rw [eq,List.filterMap_append] at same
    simpa using same
  have safe : Safe (runPrefix g w h).2 := by rw [eq]; exact hi.quiet_suffix excluded
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

theorem state_quiet {g : WGPrefix Journal.Event α} (app : StateAppends g)
    (frame : StateHistoryFrame ReservationHistory.allocation? g) : Driver.StateHistorySafe Safe g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have excluded : suffix.filterMap ReservationHistory.allocation? = [] := by
    have same := frame w a h
    rw [eq,List.filterMap_append] at same
    simpa using same
  have safe : Safe (runPrefix (g.run w) a h).2 := by rw [eq]; exact hi.quiet_suffix excluded
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix (g.run w) a h).1 <;> trivial

theorem product_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, ReservationHistory.allocation? (encode e) = none) (g : PrefixM F α) :
    Driver.ProductHistorySafe Safe (focusPrefix encode decode g) :=
  product_quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ quiet _)

theorem state_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, ReservationHistory.allocation? (encode e) = none) (g : WGPrefix F α) :
    Driver.StateHistorySafe Safe (focusStatePrefix encode decode g) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ _ quiet (g.run w))

theorem lift (action : WG.M α) (frame : CoreRetains action) :
    StatePrefixPreserves (Keep (fun h w => Picked h pid slot w ∧ C)) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w a result v b hi run
  have retained := hi.2.1.transport (suffix := [])
    ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run)
  exact ⟨hi.1,(by simpa only [List.append_nil] using retained),hi.2.2⟩

theorem quiet {g : WGPrefix Journal.Event α} {native : WG.M α}
    (appends : StateAppends g) (quiet : StateHistoryFrame ReservationHistory.allocation? g)
    (erases : ErasesStatePrefix g native) (frame : CoreRetains native) :
    StatePrefixPreserves (Keep (fun h w => Picked h pid slot w ∧ C)) Safe g := by
  intro w a h hi
  obtain ⟨suffix,equal⟩ := appends w a h
  obtain ⟨_,_,safe,_⟩ := state_quiet appends quiet w a h hi.1
  refine ⟨suffix,equal,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    have original := (erases w a h).symm.trans run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b original
    refine ⟨safe,?_⟩
    rw [equal]
    exact ⟨hi.2.1.transport same,hi.2.2⟩

end Leanux.Proofs.WG.HandshakeSecurity.AllocationSelection
