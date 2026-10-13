import Leanux.Spikes.RxPoll
import Leanux.Env

/-! Compositional proof tools for the observer's caller chain. -/
namespace Leanux.Spikes.Ghost
open Leanux Leanux.WG Leanux.Env

abbrev getWorld : GhostM World := StateT.lift (get : M World)
abbrev setWorld (w : World) : GhostM Unit := StateT.lift (set w)
abbrev modifyWorld (f : World → World) : GhostM Unit := StateT.lift (modify f)

theorem erases_throw (e : Stop) : Erases (throw e : GhostM α) (throw e : M α) := by
  intro history world
  rfl

theorem erases_discard {g : GhostM α} {o : M α} (h : Erases g o) :
    Erases (discard g) (discard o) := by
  unfold Functor.discard
  exact erases_map _ h

macro "ghost_step" : tactic => `(tactic|
  first
    | contradiction
    | with_reducible assumption
    | with_reducible exact erases_pure _
    | with_reducible exact erases_throw _
    | with_reducible exact erases_liftM _
    | with_reducible exact erases_lift _
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

end Leanux.Spikes.Ghost
