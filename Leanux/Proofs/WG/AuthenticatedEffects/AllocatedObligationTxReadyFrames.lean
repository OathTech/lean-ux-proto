import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxWorkerFrames

/-! Readiness is the original guard/read prefix. It cannot change native WG
state, and true establishes the actual nonempty batch and selected head. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CausalJournal.CallbackQuiet
set_option pp.structureInstances false
set_option maxHeartbeats 600000

theorem ready_erases (first : Option (List SkbId)) : ErasesPrefix (ready first) (liftWG (txReadySource first)) := by
  have step {α : Type} (a : WG.M α) : ErasesPrefix (CausalJournal.completionOps.step a) (liftWG a) :=
    focusPrefix_erases _ _ (erasesPrefix_lift _)
  have packet (id : SkbId) : ErasesPrefix (CausalJournal.completionOps.packet id) (liftWG (getTxSkb id)) :=
    focusPrefix_erases _ _ (Completion.access_erases (getTxSkbPrefix_erases id))
  cases first <;> try (rename_i items; cases items)
  all_goals
    unfold ready txReadySource TxDisposition.andObs WG.andM
    simp only [List.head?,liftWG_bind,liftWG_pure,apply_ite]
    repeat' first
      | exact step _
      | exact packet _
      | exact erasesPrefix_pure _
      | apply erasesPrefix_bind
      | apply erasesPrefix_ite
      | maintenance_intro
      | dsimp (config := {failIfUnchanged := true}) only
      | split

theorem ready_history (ρ : CausalJournal.Event → Option F)
    (quiet : ∀ e, ρ (.old (Journal.completionEvent e)) = none) (first : Option (List SkbId)) :
    ProductQuiet ρ (ready first) := by
  apply product_of_history
  intro before
  unfold ready TxDisposition.andObs
  repeat' first
    | (exact product_history (product_focus ρ (CausalJournal.Event.old ∘ Journal.completionEvent)
        CausalJournal.completion? quiet _) before)
    | driver_product_history_step

theorem ready_entry (first : Option (List SkbId))
    (before : StagedEntry.Inv history ledger debts locals w.wg)
    (performed : runPrefix (ready first) w history = (.ok (go,v),last)) :
    StagedEntry.Inv last ledger debts locals v.wg ∧ v.wg = w.wg ∧
      (go = true → ∃ items id packet, first = some items ∧ items.head? = some id ∧
        TxDisposition.txPackets w.wg id = some packet ∧ packet.state ≠ .uncrypted) := by
  classical
  let ρ : CausalJournal.Event → Option Unit := fun event => if birthPackets event = [] then none else some ()
  have quiet := ready_history ρ (fun event => by cases event <;> simp [ρ,birthPackets,Journal.completionEvent]) first
  obtain ⟨suffix,extended⟩ := quiet.1 w history
  have filtered := quiet.2 w history
  rw [extended,List.filterMap_append] at filtered
  have empty : suffix.filterMap ρ = [] := List.append_right_eq_self.mp filtered
  have noBirth : ∀ event ∈ suffix, birthPackets event = [] := by
    intro event member
    by_cases none : birthPackets event = []
    · exact none
    have bad : () ∈ suffix.filterMap ρ := List.mem_filterMap.mpr ⟨event,member,by simp [ρ,none]⟩
    rw [empty] at bad
    cases bad
  rw [performed] at extended
  change last = history ++ suffix at extended
  have full := (ready_erases first w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases native : ((txReadySource first).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have same := (hoare_iff_run_ambient _ _ _).mp (ready_world_frame first (· = w.wg))
      w.wg w.ambient result g ambient rfl native
    refine ⟨?_,same,?_⟩
    · rw [extended,same]
      exact before.views suffix noBirth rfl rfl rfl rfl rfl rfl
    · intro truth
      subst result
      obtain ⟨items,id,packet,chosen,head,stored,marked,_⟩ := TxDispositionCoverage.ready_true w.ambient ambient native
      exact ⟨items,id,packet,chosen,head,stored,marked⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
