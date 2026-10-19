import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadHistory

/-! History frames for exact staged plaintext provenance. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchPayload
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem quiet {g : WGPrefix Journal.Event α} (appends : StateAppends g)
    (quiet : StateHistoryFrame ReservationHistory.allocation? g) (mono : Monotone P) :
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
    refine ⟨safe,?_⟩
    exact mono h _ (by intro e member; rw [equal]; exact List.mem_append_left _ member) hi.2

theorem lift (action : WG.M α) : StatePrefixPreserves (Keep P) Safe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi _ => hi)

theorem pure (value : α) : StatePrefixPreserves (Keep P) Safe (Pure.pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.TransmitSecurity.BatchPayload
