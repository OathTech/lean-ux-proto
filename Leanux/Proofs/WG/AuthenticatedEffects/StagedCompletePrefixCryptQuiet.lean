import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixFixedHistory
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRing

/-! Quiet focused sources certify each appended position separately. This
uses the old account for logical history safety; native interval provenance
is not inferred from the history frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Crypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier
open CompleteRing (demand? demand_none)

abbrev Checked (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (Safe : List Event→Prop) (body : PrefixM Event α) : Prop :=
  Ensures (CompletePoll.Carrier debts locals) Safe body (fun _=>CompletePoll.Carrier debts locals)

theorem focused_cuts (Safe : List Event→Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w→Safe h)
    (encode : E→Event) (decode : Event→Option E) (body : PrefixM E α)
    (appends : Appends body) (quiet : HistoryFrame (demand? ∘ encode) body) :
    ∀ w h, CompletePoll.Carrier debts locals h w→∃ suffix,
      (runPrefix (focusPrefix encode decode body) w h).2=h++suffix ∧ Cuts Safe h suffix := by
  intro w h before
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨suffix,extended⟩ := appends w (h.filterMap decode)
  have filtered := quiet w (h.filterMap decode)
  rw [extended,List.filterMap_append] at filtered
  have empty : suffix.filterMap (demand? ∘ encode) = [] := List.append_right_eq_self.mp filtered
  have harmless : ∀ event ∈ suffix, birthPackets (encode event) = [] ∧ Quiet (encode event) := by
    intro event member
    have absent := List.filterMap_eq_nil_iff.mp empty event member
    classical
    by_cases good : birthPackets (encode event) = [] ∧ Quiet (encode event)
    · exact good
    · simp only [Function.comp_apply,demand?,good,ite_false] at absent
      cases absent
  rw [focusPrefix_suffix encode decode body w h _ suffix (Prod.ext rfl extended)]
  refine ⟨suffix.map encode,rfl,?_⟩
  intro n _
  apply accountSafe ledger _ w.wg
  apply accounted.append_quiet
  · intro event member
    obtain ⟨original,belongs,rfl⟩ := List.mem_map.mp (List.mem_of_mem_take member)
    exact (harmless original belongs).1
  · intro event member
    obtain ⟨original,belongs,rfl⟩ := List.mem_map.mp (List.mem_of_mem_take member)
    exact (harmless original belongs).2

theorem focused (Safe : List Event→Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w→Safe h)
    (encode : E→Event) (decode : Event→Option E) (body : PrefixM E α)
    (appends : Appends body) (quiet : HistoryFrame (demand? ∘ encode) body)
    (native : Leanux.M α) (erases : ErasesPrefix body native)
    (frame : ∀ h ledger, Preserves (fun w : World=>Inv h ledger debts locals w.wg) native) :
    Checked debts locals Safe (focusPrefix encode decode body) :=
  Ensures.of_cuts (CompleteRing.focused Safe accountSafe encode decode body appends quiet native erases frame)
    (focused_cuts Safe accountSafe encode decode body appends quiet)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Crypt
