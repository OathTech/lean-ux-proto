import Leanux.Proofs.WG.Noise.DriverTagSource

/-! Projected observations of actual tag journals. Inspection runs an observer
on the supplied native state without committing its effects to the caller.
The reported outcome is still the complete original result or Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev Inspection (α : Type) := Campaign2.Outcome α × List DriverTagEvent

def inspectObserved {α : Type} (observer : Obs α) : WG.M (Inspection α) :=
  fun g ambient =>
    let out := runWGPrefix observer g ambient []
    .ok (((Campaign2.observeResult out.1,out.2),g),ambient)

/-- Every reported receipt comes from its named original helper. A normal
outcome additionally accounts for every surviving tag; a Stop exposes no
final state and asserts no coverage of incomplete helper writes. -/
def InspectionFacts {α : Type} (entry : Campaign2.Snapshot) (out : Inspection α) : Prop :=
  ValidHistory out.2 ∧ match out.1 with
    | .error _ => True
    | .ok (_,final) => DriverTagCoverage entry out.2 final

theorem inspection_facts {α : Type} (observer : Obs α)
    (preserves : ∀ entry, StatePrefixPreserves
      (fun h g _ => NativeInv entry h g) ValidHistory observer)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (inspectObserved observer) (fun s => s = entry)
      (fun out final => final = entry ∧ InspectionFacts entry out) := by
  intro g ambient out final after pre run
  cases run
  subst entry
  have start : NativeInv (responseTagMap g.dev) [] g :=
    ⟨TagsRetained.refl _,by intro event member; cases member⟩
  obtain ⟨_,_,safe,normal⟩ := preserves (responseTagMap g.dev) g ambient [] start
  refine ⟨rfl,safe,?_⟩
  cases observed : runWGPrefix observer g ambient [] with
  | mk result events =>
    cases result with
    | error stop => trivial
    | ok result =>
      obtain ⟨⟨value,current⟩,inputs⟩ := result
      simp only [runWGPrefix,runStatePrefix] at observed
      have normal' : NativeInv (responseTagMap g.dev) events current := by
        simpa only [observed] using normal
      exact normal'.1

/-- Forgetting only the returned journal gives the original inspected call,
including every failure and the same projected normal result. -/
theorem inspection_erases {α : Type} (observer : Obs α) (action : WG.M α)
    (erases : ErasesStatePrefix observer action) :
    Campaign2.AgreesOn (fun _ => True)
      (do let out ← inspectObserved observer; pure out.1) (Campaign2.inspect action) := by
  intro g ambient _
  have same := erases g ambient []
  change Campaign2.observeResult (.ok ((Campaign2.observeResult
    (runWGPrefix observer g ambient []).1,g),ambient)) = _
  change (runWGPrefix observer g ambient []).1 = (action.run g).run ambient at same
  rw [same]
  rfl

theorem peerCreate_inspection (key : Key) (psk : Option Key)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (inspectObserved (peerCreateObserved key psk)) (fun s => s = entry)
      (fun out final => final = entry ∧ InspectionFacts entry out) :=
  inspection_facts _ (fun tags => peerCreateObserved_preserves tags key psk) entry

end Leanux.Proofs.WG.Noise.DriverTags
