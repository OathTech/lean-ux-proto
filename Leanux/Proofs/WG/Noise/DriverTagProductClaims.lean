import Leanux.Proofs.WG.Noise.DriverTagClaims
import Leanux.Proofs.WG.Noise.DriverTagProductSource

/-! Product executions expose only the campaign's WireGuard projection at the
claim boundary. Source adapters still establish exact unprojected erasure. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Logged

def observeProductResult {α : Type} (out : Except Stop (α × World)) : Campaign2.Outcome α :=
  out.map fun (value,w) => (value,Campaign2.snapshot w.wg w.ambient)

def ProductEnsures {α : Type} (action : Leanux.M α)
    (pre : Campaign2.Snapshot → Prop) (post : α → Campaign2.Snapshot → Prop) : Prop :=
  ∀ w value final, pre (Campaign2.snapshot w.wg w.ambient) →
    action.run w = .ok (value,final) → post value (Campaign2.snapshot final.wg final.ambient)

def ProductAgreesOn {α : Type} (pre : Campaign2.Snapshot → Prop)
    (left right : Leanux.M α) : Prop :=
  ∀ w, pre (Campaign2.snapshot w.wg w.ambient) →
    observeProductResult (left.run w) = observeProductResult (right.run w)

def inspectProduct {α : Type} (observer : ProductObs α) : Leanux.M (Inspection α) :=
  fun w =>
    let out := runPrefix observer w []
    .ok ((observeProductResult out.1,out.2),w)

def inspectOriginalProduct {α : Type} (action : Leanux.M α) : Leanux.M (Campaign2.Outcome α) :=
  fun w => .ok (observeProductResult (action.run w),w)

theorem product_inspection_facts {α : Type} (observer : ProductObs α)
    (preserves : ∀ entry, PrefixPreserves (StateInv entry) ValidHistory observer)
    (entry : Campaign2.Snapshot) :
    ProductEnsures (inspectProduct observer) (fun s => s = entry)
      (fun out final => final = entry ∧ InspectionFacts entry out) := by
  intro w out final pre run
  cases run
  subst entry
  have start : StateInv (tagView w.wg) [] w :=
    ⟨TagsRetained.refl _,by intro event member; cases member⟩
  obtain ⟨_,_,valid,normal⟩ := preserves (tagView w.wg) w [] start
  refine ⟨rfl,valid,?_⟩
  cases observed : runPrefix observer w [] with
  | mk result events =>
    cases result with
    | error stop => trivial
    | ok out =>
      obtain ⟨value,current⟩ := out
      have normal' : StateInv (tagView w.wg) events current := by
        simpa only [observed] using normal
      exact normal'.1

theorem product_inspection_erases {α : Type} (observer : ProductObs α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) :
    ProductAgreesOn (fun _ => True)
      (do let out ← inspectProduct observer; pure out.1) (inspectOriginalProduct action) := by
  intro w _
  have same := erases w []
  change observeProductResult (.ok (observeProductResult (runPrefix observer w []).1,w)) = _
  rw [same]
  rfl

end Leanux.Proofs.WG.Noise.DriverTags

