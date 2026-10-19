import Leanux.Proofs.Logged.RxPoll
import Leanux.Env

/-! Compositional proof tools for the observer's caller chain. -/
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Env

abbrev getWorld : GhostM World := StateT.lift (get : Leanux.M World)
abbrev setWorld (w : World) : GhostM Unit := StateT.lift (set w)
abbrev modifyWorld (f : World → World) : GhostM Unit := StateT.lift (modify f)

theorem erases_throw (e : Stop) : Erases (throw e : GhostM α) (throw e : Leanux.M α) := by
  intro history
  funext world
  rfl

theorem erases_discard {g : GhostM α} {o : Leanux.M α} (h : Erases g o) :
    Erases (discard g) (discard o) := by
  unfold Functor.discard
  exact erases_map _ h

macro "ghost_step" : tactic => `(tactic|
  first
    | contradiction
    | with_reducible assumption
    | with_reducible exact erases_pure _
    | with_reducible exact erases_throw _
    | exact erases_liftM _
    | exact erases_lift _
    | with_reducible apply erases_ite
    | with_reducible apply erases_bind
    | with_reducible apply erases_discard
    | with_reducible apply erases_map
    | with_reducible apply erases_range
    | with_reducible apply erases_forIn
    | intro_forall
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, List.cons.injEq,
        Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false]))

end Leanux.Proofs.Logged
