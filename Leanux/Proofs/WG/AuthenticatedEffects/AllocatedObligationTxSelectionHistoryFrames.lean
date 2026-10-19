import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxSelectionSource

/-! Queue selection histories append only existing completion accesses and
removal events. Birth accounting is retained independently from native state
erasure, including stopped prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CausalJournal.CallbackQuiet
set_option maxHeartbeats 600000

theorem peek_history (ρ : CausalJournal.Event → Option F)
    (quiet : ∀ e, ρ (.old (Journal.completionEvent e)) = none) (pid : PeerId) :
    ProductQuiet ρ (peek pid) := by
  apply product_of_history
  intro before
  unfold peek
  repeat' first
    | (exact product_history (product_focus ρ (CausalJournal.Event.old ∘ Journal.completionEvent) CausalJournal.completion? quiet _) before)
    | driver_product_history_step

theorem drop_history (ρ : CausalJournal.Event → Option F)
    (quiet : ∀ e, ρ (.old (Journal.completionEvent e)) = none) (pid : PeerId) (items : List SkbId) :
    ProductQuiet ρ (CausalJournal.completionOps.drop pid items) :=
  product_focus ρ (CausalJournal.Event.old ∘ Journal.completionEvent) CausalJournal.completion? quiet _

private theorem suffix_quiet {action : PrefixM CausalJournal.Event α}
    (kept : ∀ ρ : CausalJournal.Event → Option Unit,
      (∀ e, ρ (.old (Journal.completionEvent e)) = none) → ProductQuiet ρ action)
    (w : World) (history : List CausalJournal.Event) :
    ∃ suffix, (runPrefix action w history).2 = history ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] := by
  classical
  let ρ : CausalJournal.Event → Option Unit := fun event => if birthPackets event = [] then none else some ()
  have quiet := kept ρ (fun event => by cases event <;> simp [ρ,birthPackets,Journal.completionEvent])
  obtain ⟨suffix,extended⟩ := quiet.1 w history
  refine ⟨suffix,extended,?_⟩
  have filtered := quiet.2 w history
  rw [extended,List.filterMap_append] at filtered
  have empty : suffix.filterMap ρ = [] := List.append_right_eq_self.mp filtered
  intro event member
  by_cases none : birthPackets event = []
  · exact none
  have bad : () ∈ suffix.filterMap ρ := List.mem_filterMap.mpr ⟨event,member,by simp [ρ,none]⟩
  rw [empty] at bad
  cases bad

theorem peek_birth_quiet (pid : PeerId) (w : World) (history : List CausalJournal.Event) :
    ∃ suffix, (runPrefix (peek pid) w history).2 = history ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] :=
  suffix_quiet (fun ρ quiet => peek_history ρ quiet pid) w history

theorem drop_birth_quiet (pid : PeerId) (items : List SkbId) (w : World) (history : List CausalJournal.Event) :
    ∃ suffix, (runPrefix (CausalJournal.completionOps.drop pid items) w history).2 = history ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] :=
  suffix_quiet (fun ρ quiet => drop_history ρ quiet pid items) w history

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxSelection
