import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryEncryptFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPassive
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedEncryption

/-! Full local Entry transport through the actual encryption callback.
History and native state are proved separately. The stopped certificate is a
retained accounted entry, not a claim about a hidden final native world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Encrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation Staged.Obligations CausalJournal

/-- Every event appended by this callback is birth-free, including its
publication's original peer-release observer and stopped prefixes. -/
theorem history (items : Option (List SkbId)) (w : World) (h : List Event) :
    ∃ suffix, (runPrefix (CausalJournal.encrypt items) w h).2 = h ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] := by
  classical
  let ρ : Event → Option Unit := fun event => if birthPackets event = [] then none else some ()
  have quiet := CallbackQuiet.encrypt ρ (fun _ => by simp [ρ,birthPackets])
    (fun _ => by simp [ρ,birthPackets]) (fun _ _ => by simp [ρ,birthPackets]) items
  obtain ⟨suffix,extended⟩ := quiet.1 w h
  refine ⟨suffix,extended,?_⟩
  have filtered := quiet.2 w h
  rw [extended,List.filterMap_append] at filtered
  have empty : suffix.filterMap ρ = [] := List.append_right_eq_self.mp filtered
  intro event member
  by_cases noBirth : birthPackets event = []
  · exact noBirth
  have bad : () ∈ suffix.filterMap ρ := List.mem_filterMap.mpr ⟨event,member,by simp [ρ,noBirth]⟩
  rw [empty] at bad
  cases bad

theorem erases (items : Option (List SkbId)) :
    ErasesPrefix (CausalJournal.encrypt items) (RxWorkers.encryptStepTailSource items) := by
  apply CallbackFrames.product_erases old? (CausalJournal.encrypt_projects items)
  intro w h
  have projected := congrArg Prod.fst (Journal.encrypt_projects items w h)
  have maps : (fun x : Bool × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
  rw [maps,Except.map_id] at projected
  exact projected.symm

/-- Encryption keeps the fixed ledger, cleanup debts and owning locations;
only bytes, publication state and scheduling may change. -/
theorem checked (items : Option (List SkbId)) :
    PrefixPreserves (fun h w => Inv h ledger debts locals w.wg)
      (Passive.Safe ledger debts locals) (CausalJournal.encrypt items) := by
  intro w h before
  obtain ⟨suffix,extended,quiet⟩ := history items w h
  refine ⟨suffix,extended,?_,?_⟩
  · rw [extended]
    exact ⟨w.wg,Queued.Inv.history before suffix quiet⟩
  · cases result : (runPrefix (CausalJournal.encrypt items) w h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨value,v⟩ := out
      have native := (erases items w h).symm.trans result
      have kept := (hoare_iff_run _ _ _).mp (tail items) w value v before native
      rw [extended]
      exact Queued.Inv.history kept suffix quiet

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Encrypt
