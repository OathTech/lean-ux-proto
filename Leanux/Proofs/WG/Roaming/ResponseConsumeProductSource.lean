import Leanux.Proofs.WG.Roaming.ResponseConsumeSource
import Leanux.Proofs.WG.Roaming.ResponseConsumeProductModel

namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

/-- Lift the actual native tail once and retain the entry fixture observation. -/
def responseConsumeTail (msg : List UInt8) (input : ResponseInput) : M (Option ResponseConsumed) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.responseConsumeTail msg input)
  pure (out.map fun cut => ⟨cut, fixture⟩)

/-- The full native consumer with its original product observations restored. -/
def responseConsume (msg : List UInt8) : M (Option ResponseConsumed) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.responseConsume msg)
  pure (out.map fun cut => ⟨cut, fixture⟩)

def responsePeer (out : Option ResponseConsumed) : Option PeerId :=
  out.map fun cut => cut.input.pid

/-- The product decoration erases to the actual lifted consumer, including Stops. -/
theorem responseConsume_erase (msg : List UInt8) :
    (do let out ← responseConsume msg; pure (responsePeer out)) =
      liftWG (consumeResponse msg) := by
  rw [← Roaming.responseConsume_erase]
  funext w
  dsimp only [responseConsume, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.responseConsume msg).run w.wg).run w.ambient with
  | error err => simp [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    cases out <;> rfl

/-- Every successful product transcript records the actual full successor
observation. The crypto and commit clauses are the native facts unchanged. -/
theorem responseConsumeTail_facts (msg : List UInt8) (input : ResponseInput)
    (identity : input.identity.hasIdentity = true)
    (state : input.peer.handshakeState = HANDSHAKE_CREATED_INITIATION) :
    Campaign2.Product.Ensures (responseConsumeTail msg input) (fun _ => True)
      (fun result observed => ∀ cut, result = some cut → cut.input = input ∧
        cut.committedSnapshot = observed ∧ ResponseConsumedFacts msg cut) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [responseConsumeTail, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.responseConsumeTail msg input).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at native
    rw [native] at run
    cases out with
    | none => cases run
    | some value =>
      simp only [Option.map_some, Except.ok.injEq,
        Prod.mk.injEq, Option.some.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      have facts := Roaming.responseConsumeTail_facts msg input identity state
        w.wg w.ambient (some value) current after trivial native value rfl
      exact ⟨facts.1, by simp [ResponseConsumed.committedSnapshot,
        Campaign2.Product.snapshot, facts.2.1], facts.2.2⟩

end Leanux.Proofs.WG.Roaming.Product
