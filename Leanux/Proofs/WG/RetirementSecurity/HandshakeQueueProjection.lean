import Leanux.Proofs.WG.TransmitSecurity.JournalProjection

/-! Exact composition is applied to concrete source operations. It does not
infer an arbitrary higher-order hook projection from endpoint erasure. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Projection
open Leanux Leanux.Proofs.Logged

theorem product {ρ : E→Option F} {σ : F→Option G} {p : α→β} {q : β→γ}
    {a : PrefixT E State α} {b : PrefixT F State β} {c : PrefixT G State γ}
    (first : ProjectsPrefix ρ p a b) (second : ProjectsPrefix σ q b c) :
    ProjectsPrefix (fun e=>(ρ e).bind σ) (q ∘ p) a c := by
  intro w h
  rw [←List.filterMap_filterMap,second,first]
  simp only [List.filterMap_filterMap,Function.comp_def]
  cases (runPrefix a w h).1 <;> rfl

theorem state {ρ : E→Option F} {σ : F→Option G} {p : α→β} {q : β→γ}
    {a : StatePrefixT E Outer Inner α} {b : StatePrefixT F Outer Inner β} {c : StatePrefixT G Outer Inner γ}
    (first : StateProjectsPrefix ρ p a b) (second : StateProjectsPrefix σ q b c) :
    StateProjectsPrefix (fun e=>(ρ e).bind σ) (q ∘ p) a c := by
  intro w x h
  rw [←List.filterMap_filterMap,second,first]
  simp only [List.filterMap_filterMap,Function.comp_def]
  cases (runPrefix (a.run w) x h).1 <;> rfl

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Projection
