import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionProduct

/-! Source-composition rules for product-state egress accounting. Lexical
bookkeeping contributes no datagram occurrences; callbacks retain their own
precise contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem product_scope (cause : Cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (safe : ∀ token, ProductSafe (body token)) : ProductSafe (CausalScope.prefixScope Event.scope cause body) := by
  intro w h hi
  exact product_bind (product_emit (.scope (.entered ⟨h.length,cause⟩)) rfl)
    (fun _ => product_bind (safe ⟨h.length,cause⟩) (fun result =>
      product_bind (product_emit (.scope (.exited h.length)) rfl) (fun _ => product_pure result))) w h hi

theorem product_capture (body : PrefixM Event α) (safe : ProductSafe body) :
    ProductSafe (captureObserved body) := safe.captureObserved

macro "emission_product_step" : tactic => `(tactic| first
  | (emission_head Pure.pure; exact product_pure _)
  | (emission_head Bind.bind; apply product_bind)
  | (emission_head ite; apply product_ite)
  | (emission_head ForIn.forIn; apply product_forIn)
  | (emission_head captureObserved; apply product_capture)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
