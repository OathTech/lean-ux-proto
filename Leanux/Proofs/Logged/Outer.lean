import Leanux.Proofs.Logged.Basic

/-! Product-world observations at the runner boundary retain the operation
index on every original failure. -/
namespace Leanux.Proofs.Logged
open Leanux

/-- Move the observer history outside one explicit World execution, attaching
exactly the runner's operation index to any original failure. -/
def runAtLogged (index : Nat) (world : World) (g : GhostM α) :
    StateT History (Except (Nat × Stop)) (α × World) := fun history =>
  (((g.run history).run world).map (fun ((a, h), w) => ((a, w), h))).mapError
    (fun e => (index, e))

theorem runAtLogged_erases (index : Nat) (world : World) (g : GhostM α) (o : Leanux.M α)
    (h : Erases g o) :
    ErasesT (runAtLogged index world g) ((o.run world).mapError (fun e => (index, e))) := by
  intro history
  rw [← erases_run h history world]
  unfold runAtLogged
  cases he : (g.run history).run world with
  | error e => exact (congrArg (fun r => Prod.fst <$> (r.map (fun ((a, h), w) => ((a, w), h))).mapError (fun e => (index, e))) he).trans (by rfl)
  | ok out =>
    rcases out with ⟨⟨a, hist⟩, w⟩
    exact (congrArg (fun r => Prod.fst <$> (r.map (fun ((a, h), w) => ((a, w), h))).mapError (fun e => (index, e))) he).trans (by rfl)


end Leanux.Proofs.Logged
