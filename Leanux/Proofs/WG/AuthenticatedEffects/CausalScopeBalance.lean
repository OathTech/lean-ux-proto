import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeContracts

/-! A successful lexical callback closes exactly its own scope; a stopped body
keeps the entered prefix. These equations do not treat a scope as authorized. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
open Leanux Leanux.Proofs.Logged

theorem stack_enter_exit (history : List (Event Cause)) (token : Token Cause) :
    stack (history ++ [.entered token,.exited token.position]) = stack history := by
  simp only [stack,List.foldl_append,List.foldl_cons,List.foldl_nil]
  cases history.foldl advance (.ok []) <;> simp [advance] <;> rfl

theorem scope_normal_stack (record : Event Cause → E)
    (decode : E → Option (Event Cause)) (inverse : ∀ e, decode (record e) = some e)
    (cause : Cause) (body : WGPrefix E α) (frame : StateHistoryFrame decode body)
    (w v : WGWorld) (a b : Ambient) (h history : List E) (value : α)
    (normal : runWGPrefix (scope record cause body) w a h = (.ok ((value,v),b),history)) :
    stack (history.filterMap decode) = stack (h.filterMap decode) := by
  rw [scope,withToken_run] at normal
  cases run : runWGPrefix body w a (h ++ [record (.entered ⟨h.length,cause⟩)]) with
  | mk result output =>
    rw [run] at normal
    cases result with
    | error stop => cases normal
    | ok result =>
      cases normal
      have same := frame w a (h ++ [record (.entered ⟨h.length,cause⟩)])
      change (runWGPrefix body w a (h ++ [record (.entered ⟨h.length,cause⟩)])).2.filterMap decode = _ at same
      rw [run] at same
      simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,inverse] at same ⊢
      rw [same]
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using
        stack_enter_exit (h.filterMap decode) (Token.mk h.length cause)

/-- A normal callback cannot leave a stale causal token for the next worker. -/
theorem scope_normal_current (record : Event Cause → E)
    (decode : E → Option (Event Cause)) (inverse : ∀ e, decode (record e) = some e)
    (cause : Cause) (body : WGPrefix E α) (frame : StateHistoryFrame decode body)
    (w v : WGWorld) (a b : Ambient) (h history : List E) (value : α)
    (normal : runWGPrefix (scope record cause body) w a h = (.ok ((value,v),b),history)) :
    current decode history = current decode h := by
  unfold current
  rw [scope_normal_stack record decode inverse cause body frame w v a b h history value normal]

end Leanux.Proofs.WG.AuthenticatedEffects.CausalScope
