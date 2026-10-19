import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceEvents

/-! Native entry-view frames and independently checked event quietness combine
for passive observers. Erasure supplies only native endpoints: append/quiet
evidence separately accounts for the history even if the observer stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SourceQuiet
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal SourcePassive

def birth? (event : Event) : Option Event := if (birthPackets event).isEmpty then none else some event

theorem birth_none {event : Event} (quiet : birthPackets event = []) : birth? event = none := by
  simp only [birth?,quiet,List.isEmpty_nil,ite_true]

theorem quiet_suffix {body : WGPrefix Event α} (appends : StateAppends body)
    (quiet : StateHistoryFrame birth? body) (w : WGWorld) (a : Ambient) (h : List Event) :
    ∃ suffix, (runWGPrefix body w a h).2 = h ++ suffix ∧ ∀ event ∈ suffix, birthPackets event = [] := by
  obtain ⟨suffix,grown⟩ := appends w a h
  have filtered := quiet w a h
  change (runWGPrefix body w a h).2.filterMap birth? = h.filterMap birth? at filtered
  change (runWGPrefix body w a h).2 = h ++ suffix at grown
  rw [grown,List.filterMap_append] at filtered
  have empty : suffix.filterMap birth? = [] :=
    List.append_cancel_left (as := h.filterMap birth?) (by simpa only [List.append_nil] using filtered)
  refine ⟨suffix,grown,?_⟩
  intro event member
  have absent := List.filterMap_eq_nil_iff.mp empty event member
  cases payload : birthPackets event with
  | nil => rfl
  | cons packet rest => simp [birth?,payload] at absent

theorem checked {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
    (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
    {body : WGPrefix Event α} {native : WG.M α}
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (quiet : StateHistoryFrame birth? body) (frame : SameView StagedEntry.view native) :
    Checked debts locals Safe body := by
  intro w a h before
  obtain ⟨ledger,entry⟩ := before
  obtain ⟨suffix,grown,quietSuffix⟩ := quiet_suffix appends quiet w a h
  change (runPrefix (body.run w) a h).2 = h ++ suffix at grown
  have atHistory := Queued.Inv.history entry suffix quietSuffix
  refine ⟨suffix,grown,?_,?_⟩
  · rw [grown]
    exact entrySafe ledger _ w atHistory
  · cases performed : (runPrefix (body.run w) a h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have run := erases w a h
      change (runPrefix (body.run w) a h).1 = _ at run
      rw [performed] at run
      have view := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run.symm
      change ∃ ledger, Inv (runPrefix (body.run w) a h).2 ledger debts locals v
      rw [grown]
      exact ⟨ledger,atHistory.same_view view⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.SourceQuiet
