import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceNeutral
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePollMatching

/-! One callback wrapper per actual GRO output packet. Its argument is the
buffered occurrence, even when that packet was held while another candidate
was being consumed. Neutral wrapping is exactly the existing batch callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged

def stackWith (scope : Entry → PrefixM E Unit → PrefixM E Unit)
    (callback : List UInt8 → PrefixM E Unit) (entries : List Entry) : PrefixM E Unit :=
  entries.forM fun entry => scope entry (callback entry.bytes)

theorem stack_neutral (callback : List UInt8 → PrefixM E Unit) (entries : List Entry) :
    stackWith (fun _ body => body) callback entries = (entries.map Entry.bytes).forM callback := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [stackWith, List.forM_eq_forM, List.forM_cons, List.map_cons] at *
    rw [ih]

theorem stack_matching (ρ : E → Option F) (scopeMap : Nat → Nat)
    (scope : Entry → PrefixM E Unit → PrefixM E Unit)
    (targetScope : Entry → PrefixM F Unit → PrefixM F Unit)
    (callback : List UInt8 → PrefixM E Unit) (target : List UInt8 → PrefixM F Unit)
    (projects : ∀ bytes, ProjectsPrefix ρ id (callback bytes) (target bytes))
    (wrapped : ∀ entry body targetBody, ProjectsPrefix ρ id body targetBody →
      ProjectsPrefix ρ id (scope entry body) (targetScope (entry.map scopeMap) targetBody))
    (entries : List Entry) :
    ProjectsPrefix ρ id (stackWith scope callback entries)
      (stackWith targetScope target (entries.map (Entry.map scopeMap))) := by
  induction entries with
  | nil => exact projectsPrefix_pure ρ id ()
  | cons entry entries ih =>
    simp only [stackWith, List.forM_eq_forM, List.forM_cons, List.map_cons] at *
    exact projectsPrefix_bind ρ id id (wrapped entry _ _ (projects entry.bytes)) (fun _ => ih)

theorem stack_projects (ρ : E → Option F)
    (scope : Entry → PrefixM E Unit → PrefixM E Unit)
    (callback : List UInt8 → PrefixM E Unit) (target : List UInt8 → PrefixM F Unit)
    (projects : ∀ bytes, ProjectsPrefix ρ id (callback bytes) (target bytes))
    (quiet : ∀ entry body targetBody, ProjectsPrefix ρ id body targetBody →
      ProjectsPrefix ρ id (scope entry body) targetBody)
    (entries : List Entry) :
    ProjectsPrefix ρ id (stackWith scope callback entries)
      ((entries.map Entry.bytes).forM target) := by
  induction entries with
  | nil => exact projectsPrefix_pure ρ id ()
  | cons entry entries ih =>
    simp only [stackWith, List.forM_eq_forM, List.forM_cons, List.map_cons] at *
    exact projectsPrefix_bind ρ id id (quiet entry _ _ (projects entry.bytes)) (fun _ => ih)

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
