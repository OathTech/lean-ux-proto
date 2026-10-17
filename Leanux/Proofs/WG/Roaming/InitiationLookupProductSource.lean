import Leanux.Proofs.WG.Roaming.InitiationLookupSource
import Leanux.Proofs.WG.Roaming.InitiationLookupProductModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

/-- Observe the lifted lookup on a copy, then execute it from the same entry. -/
def initiationLookup (key : Key) : M InitiationLookup := do
  let before ← Campaign2.Product.read
  let observed ← Campaign2.Product.inspect (liftWG (pubkeyLookup key))
  let result ← liftWG (pubkeyLookup key)
  let after ← Campaign2.Product.read
  return ⟨before, observed, result, after⟩

/-- Every original product continuation receives the exact actual successor. -/
theorem initiationLookup_bind {α : Type} (key : Key) (next : Option PeerId → M α) :
    (initiationLookup key >>= fun out => next out.result) = (liftWG (pubkeyLookup key) >>= next) := by
  funext entry
  change (((liftWG (pubkeyLookup key)).run entry >>= fun pair =>
    Except.ok (InitiationLookup.mk (Campaign2.Product.snapshot entry)
      (Campaign2.Product.observeResult ((liftWG (pubkeyLookup key)).run entry)) pair.1
      (Campaign2.Product.snapshot pair.2), pair.2)) >>= fun out => next out.1.result out.2) =
    ((liftWG (pubkeyLookup key)).run entry >>= fun out => next out.1 out.2)
  cases run : (liftWG (pubkeyLookup key)).run entry <;> rfl

theorem initiationLookup_facts (key : Key) :
    Campaign2.Product.Ensures (initiationLookup key) (fun _ => True)
      (fun out _ => ∀ pid, out.result = some pid → InitiationLookupFacts key pid out) := by
  intro entry out final _ run
  change ((liftWG (pubkeyLookup key)).run entry >>= fun pair =>
    Except.ok (InitiationLookup.mk (Campaign2.Product.snapshot entry)
      (Campaign2.Product.observeResult ((liftWG (pubkeyLookup key)).run entry)) pair.1
      (Campaign2.Product.snapshot pair.2), pair.2)) = .ok (out, final) at run
  dsimp only [liftWG, StateT.run, Bind.bind, Pure.pure, Except.bind, Except.pure] at run
  cases lookup : ((pubkeyLookup key).run entry.wg).run entry.ambient with
  | error err => simp only [StateT.run] at lookup; rw [lookup] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨result, current⟩, last⟩
    simp only [StateT.run] at lookup
    rw [lookup] at run
    simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    intro pid selected
    have facts := Roaming.initiation_pubkey_provenance key (Campaign2.snapshot entry.wg entry.ambient)
      entry.wg entry.ambient result current last rfl lookup pid selected
    change result = some pid at selected
    subst result
    exact ⟨rfl, rfl, facts⟩

end Leanux.Proofs.WG.Roaming.Product
