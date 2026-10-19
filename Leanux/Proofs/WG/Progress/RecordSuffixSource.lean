import Leanux.Proofs.WG.Progress.RecordSuffixModel
import Leanux.Proofs.WG.Progress.RecordSuffixFrames
import Leanux.Proofs.WG.Progress.CutSource
import Leanux.Proofs.WG.Progress.CookieControlSource
import Leanux.Proofs.Framing.Hoare
/-! Concrete record consumers and rescheduling. All conclusions concern original normal returns; no successful callback, record validity, final suffix or whole-activation termination is assumed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Env Leanux.Proofs.Framing

theorem skipAmbient_suffix (records : List HiddenRecord) :
    Hoare AmbientM.skipAmbient (fun a => a.hidden = some records)
      (fun _ a => Tail records a.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after present run
  rw [skipAmbient_run before records present] at run
  cases run
  exact ⟨_,rfl,List.dropWhile_suffix _⟩

theorem hidden_suffix (site : HiddenSite) (records : List HiddenRecord) :
    Hoare (AmbientM.hidden site) (fun a => a.hidden = some records)
      (fun _ a => StrictTail records a.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after present run
  let stripped := records.dropWhile (fun r => HiddenSite.passive r.site)
  let skipped : Ambient := {before with hidden := some stripped}
  let marked : Ambient := if site.info.id == (HiddenSite.sectionStart .netRx).info.id then
    {skipped with netRxSections := skipped.netRxSections + 1} else skipped
  have markRun : (AmbientM.noteNetRxStart site.info.id).run skipped = .ok ((),marked) := by
    unfold AmbientM.noteNetRxStart marked
    split <;> rfl
  have markedHidden : marked.hidden = some stripped := by
    unfold marked
    split <;> rfl
  simp only [AmbientM.hidden,StateT.run_bind,skipAmbient_run before records present] at run
  change ((AmbientM.noteNetRxStart site.info.id).run skipped >>= _) = _ at run
  rw [markRun] at run
  simp only [StateT.run_get,pure_bind] at run
  dsimp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at run
  rw [markedHidden] at run
  have suffix := List.dropWhile_suffix (l := records) (fun r => HiddenSite.passive r.site)
  change stripped.IsSuffix records at suffix
  cases shape : stripped with
  | nil => simp only [shape] at run; cases run
  | cons record rest =>
    rw [shape] at suffix
    simp only [shape] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases site <;> cases run
        all_goals
          refine ⟨rest,rfl,(List.suffix_cons record rest).trans suffix,?_⟩
          have length := suffix.length_le
          simp only [List.length_cons] at length
          omega

theorem retain_tail {σ α : Type} (read : σ → Option (List HiddenRecord))
    (action : StateT σ (Except Stop) α)
    (spec : ∀ records, Hoare action (fun w => read w = some records)
      (fun _ w => Tail records (read w))) (records : List HiddenRecord) :
    Preserves (fun w => Tail records (read w)) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  obtain ⟨middle,present,prior⟩ := pre
  exact tail_extend prior ((hoare_iff_run _ _ _).mp (spec middle)
    before value after present run)

theorem hidden_product_suffix (site : HiddenSite) (records : List HiddenRecord) :
    Hoare (hidden site : Leanux.M (List UInt8))
      (fun w => w.ambient.hidden = some records)
      (fun _ w => StrictTail records w.ambient.hidden) :=
  liftAmbient_contract _ _ _ (hidden_suffix site records)

theorem skip_product_suffix (records : List HiddenRecord) :
    Hoare (skipAmbient : Leanux.M Unit) (fun w => w.ambient.hidden = some records)
      (fun _ w => Tail records w.ambient.hidden) :=
  liftAmbient_contract _ _ _ (skipAmbient_suffix records)

theorem peek_product_suffix (records : List HiddenRecord) :
    Hoare (peekHiddenSite : Leanux.M (Option Nat))
      (fun w => w.ambient.hidden = some records)
      (fun _ w => Tail records w.ambient.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after present run
  rw [cookiePeek_run before records present] at run
  cases run
  exact ⟨_,rfl,List.dropWhile_suffix _⟩

theorem condResched_suffix (worker : Worker) (records : List HiddenRecord) :
    Hoare (condResched worker) (fun w => w.ambient.hidden = some records)
      (fun yielded w => Tail records w.ambient.hidden ∧
        (yielded = true → StrictTail records w.ambient.hidden)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after present run
  unfold condResched at run
  cases choice : worker.resched? with
  | none => simp only [choice] at run; cases run
  | some site =>
    simp only [choice,StateT.run_bind,cookiePeek_run before records present] at run
    let rest := records.dropWhile fun r => HiddenSite.passive r.site
    let skipped := {before with ambient := {before.ambient with hidden := some rest}}
    change ((if rest.head?.map (·.site) != some site.info.id then pure false else
      do let _ ← hidden site; pure true : Leanux.M Bool).run skipped) =
      .ok (value,after) at run
    have prior : rest.IsSuffix records := List.dropWhile_suffix _
    split at run
    · have outputs : (false,skipped) = (value,after) := Except.ok.inj run
      have valueEq : value = false := (congrArg Prod.fst outputs).symm
      have afterEq : after = skipped := (congrArg Prod.snd outputs).symm
      rw [valueEq,afterEq]
      exact ⟨⟨rest,rfl,prior⟩,by intro impossible; cases impossible⟩
    · rw [StateT.run_bind] at run
      cases read : (hidden site : Leanux.M (List UInt8)).run skipped with
      | error error => rw [read] at run; cases run
      | ok pair =>
        obtain ⟨bytes,middle⟩ := pair
        rw [read] at run
        cases run
        have strict := strict_extend prior ((hoare_iff_run _ _ _).mp
          (hidden_product_suffix site rest) skipped bytes middle rfl read)
        exact ⟨strict_tail strict,fun _ => strict⟩

theorem condResched_retains (worker : Worker) (records : List HiddenRecord) :
    Preserves (fun w => Tail records w.ambient.hidden) (condResched worker) :=
  retain_tail (fun w : World => w.ambient.hidden) _ (fun input =>
    hoare_consequence (condResched_suffix worker input) (fun _ h => h)
      (fun _ _ h => h.1)) records


theorem hidden_after_tail (site : HiddenSite) (records : List HiddenRecord) :
    Hoare (AmbientM.hidden site) (fun a => Tail records a.hidden)
      (fun _ a => StrictTail records a.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  obtain ⟨middle,present,prior⟩ := pre
  exact strict_extend prior ((hoare_iff_run _ _ _).mp
    (hidden_suffix site middle) before value after present run)

theorem hidden_after_product_tail (site : HiddenSite) (records : List HiddenRecord) :
    Hoare (hidden site : Leanux.M (List UInt8))
      (fun w => Tail records w.ambient.hidden)
      (fun _ w => StrictTail records w.ambient.hidden) :=
  liftAmbient_contract _ _ _ (hidden_after_tail site records)

theorem skip_retains (records : List HiddenRecord) :
    Preserves (fun w => Tail records w.ambient.hidden) (skipAmbient : Leanux.M Unit) :=
  retain_tail (fun w : World => w.ambient.hidden) _ skip_product_suffix records

theorem peek_retains (records : List HiddenRecord) :
    Preserves (fun w => Tail records w.ambient.hidden)
      (peekHiddenSite : Leanux.M (Option Nat)) :=
  retain_tail (fun w : World => w.ambient.hidden) _ peek_product_suffix records
end Leanux.Proofs.WG.Progress.RecordSuffix
