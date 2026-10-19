import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterialSource

/-! History-only frames for actors that cannot allocate TX packets. Native
state changes are unrestricted here; only the absence of allocation events
is used to retain previously checked material-bank claims. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity Driver

theorem product_quiet {g : PrefixM Journal.Event α} (app : Appends g)
    (frame : HistoryFrame ReservationHistory.allocation? g) : ProductHistorySafe Safe g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := app w h
  have excluded : suffix.filterMap ReservationHistory.allocation? = [] := by
    have same := frame w h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap ReservationHistory.allocation? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix g w h).2 := by rw [eq]; exact hi.quiet_suffix excluded
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix g w h).1 <;> trivial

theorem state_quiet {g : WGPrefix Journal.Event α} (app : StateAppends g)
    (frame : StateHistoryFrame ReservationHistory.allocation? g) : StateHistorySafe Safe g := by
  intro w a h hi
  obtain ⟨suffix,eq⟩ := app w a h
  have excluded : suffix.filterMap ReservationHistory.allocation? = [] := by
    have same := frame w a h
    rw [eq,List.filterMap_append] at same
    have lengths := congrArg List.length same
    cases found : suffix.filterMap ReservationHistory.allocation? with
    | nil => rfl
    | cons e es =>
      simp only [List.length_append,found,List.length_cons] at lengths
      omega
  have safe : Safe (runPrefix (g.run w) a h).2 := by rw [eq]; exact hi.quiet_suffix excluded
  refine ⟨suffix,eq,safe,?_⟩
  cases (runPrefix (g.run w) a h).1 <;> trivial

theorem product_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, ReservationHistory.allocation? (encode e) = none) (g : PrefixM F α) :
    ProductHistorySafe Safe (focusPrefix encode decode g) :=
  product_quiet (Appends.focus _ _ _) (focusPrefix_other _ _ _ quiet _)

theorem state_focus (encode : F → Journal.Event) (decode : Journal.Event → Option F)
    (quiet : ∀ e, ReservationHistory.allocation? (encode e) = none) (g : WGPrefix F α) :
    StateHistorySafe Safe (focusStatePrefix encode decode g) :=
  state_quiet (StateAppends.focus _ _ _) (fun w => focusPrefix_other _ _ _ quiet (g.run w))

end Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
