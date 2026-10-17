import Leanux.Proofs.WG.Roaming.ResponseLookupSource
import Leanux.Proofs.WG.Roaming.ResponseLookupProductModel
import Leanux.Proofs.WG.Roaming.ResponseConsumeProductSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

def responseLookupRead (msg : List UInt8) : M ResponseLookupRead := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.responseLookupRead msg)
  return restoreResponseLookupRead fixture out

def responseLookupPrefix (msg : List UInt8) : M (Option ResponseLookupCut) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.responseLookupPrefix msg)
  return out.map (restoreResponseLookupCut fixture)

def responseEntrySuffix (msg : List UInt8) (entry : Option ResponseLookupCut) :
    M (Option ResponseConsumed) := do
  match entry with
  | none => return none
  | some entry => responseConsumeTail msg entry.input

def responseWithLookup (msg : List UInt8) : M (Option (ResponseLookupCut × ResponseConsumed)) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.responseWithLookup msg)
  return out.map fun (entry, consumed) => (restoreResponseLookupCut fixture entry, ⟨consumed, fixture⟩)

theorem responseLookupRead_bind {α : Type} (msg : List UInt8)
    (next : Option (IndexOwner × PeerId) → M α) :
    (responseLookupRead msg >>= fun out => next out.entry) =
      (liftWG (indexLookup [.handshake] (u32le msg 8)) >>= next) := by
  have erase : (do let out ← Roaming.responseLookupRead msg; pure out.entry) =
      indexLookup [.handshake] (u32le msg 8) := by
    simpa using Roaming.responseLookupRead_bind msg pure
  rw [← erase]
  funext w
  dsimp only [responseLookupRead, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.responseLookupRead msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    rfl

theorem responseConsume_lookup (msg : List UInt8) :
    (responseLookupPrefix msg >>= responseEntrySuffix msg) = responseConsume msg := by
  unfold responseConsume
  rw [← Roaming.responseConsume_lookup]
  funext w
  dsimp only [responseLookupPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases firstRun : ((Roaming.responseLookupPrefix msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at firstRun; rw [firstRun]
  | ok pair =>
    rcases pair with ⟨⟨entry, current⟩, middle⟩
    simp only [StateT.run] at firstRun
    rw [firstRun]
    cases entry with
    | none => rfl
    | some entry =>
      dsimp only [Option.map, responseEntrySuffix, Roaming.responseEntrySuffix,
        responseConsumeTail, restoreResponseLookupCut, Campaign2.Product.read, liftWG,
        StateT.run, StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure,
        Functor.map, Except.bind, Except.pure]
      cases tailRun : ((Roaming.responseConsumeTail msg entry.input).run current).run middle with
      | error err => simp only [StateT.run] at tailRun; rw [tailRun]
      | ok pair =>
        rcases pair with ⟨⟨out, last⟩, ending⟩
        simp only [StateT.run] at tailRun
        rw [tailRun]
        rfl

theorem responseWithLookup_consume (msg : List UInt8) :
    (do let out ← responseWithLookup msg; pure (out.map Prod.snd)) = responseConsume msg := by
  unfold responseConsume
  rw [← Roaming.responseWithLookup_consume]
  funext w
  dsimp only [responseWithLookup, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.responseWithLookup msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    cases out <;> rfl

theorem responseWithLookup_erase (msg : List UInt8) :
    (do let out ← responseWithLookup msg; pure (out.map fun pair => pair.2.input.pid)) =
      liftWG (consumeResponse msg) := by
  rw [← responseConsume_erase, ← responseWithLookup_consume]
  simp only [bind_assoc, pure_bind, responsePeer, Option.map_map, Function.comp_def]

theorem responseLookupRead_facts (msg : List UInt8) (identity : StaticIdentity) :
    Campaign2.Product.Ensures (responseLookupRead msg)
      (fun s => s.wg.device.map Device.staticIdentity = some identity)
      (fun out s => out.before.wg.device.map Device.staticIdentity = some identity ∧
        out.after.wg.device = s.wg.device ∧ out.observed = .ok (out.entry, out.after)) := by
  intro w out final pre run
  dsimp only [responseLookupRead, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.responseLookupRead msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, current⟩, after⟩
    simp only [StateT.run] at native
    rw [native] at run
    cases run
    have facts := Roaming.responseLookupRead_facts msg identity
      w.wg w.ambient value current after pre native
    exact ⟨facts.1, facts.2.1, by simp [restoreResponseLookupRead, facts.2.2, Except.map]⟩

theorem responseLookupPrefix_facts (msg : List UInt8) :
    Campaign2.Product.Ensures (responseLookupPrefix msg) (fun _ => True)
      (fun out _ => ∀ cut, out = some cut → ResponseLookupFacts cut) := by
  intro w out final _ run cut returned
  subst out
  dsimp only [responseLookupPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.responseLookupPrefix msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, current⟩, after⟩
    simp only [StateT.run] at native
    rw [native] at run
    cases value with
    | none => cases run
    | some value =>
      simp only [Option.map_some, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      have facts := Roaming.responseLookupPrefix_facts msg
        w.wg w.ambient (some value) current after trivial native value rfl
      exact ⟨facts.1, by simp [restoreResponseLookupCut, restoreResponseLookupRead, facts.2.1, Except.map],
        facts.2.2⟩

theorem responseWithLookup_facts (msg : List UInt8) :
    Campaign2.Product.Ensures (responseWithLookup msg) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        ResponseLookupFacts cut.1 ∧ cut.2.input = cut.1.input ∧
        cut.2.committedSnapshot = s ∧ ResponseConsumedFacts msg cut.2) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [responseWithLookup, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.responseWithLookup msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, current⟩, after⟩
    simp only [StateT.run] at native
    rw [native] at run
    cases value with
    | none => cases run
    | some value =>
      rcases value with ⟨entry, consumed⟩
      simp only [Option.map_some, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      have facts := Roaming.responseWithLookup_facts msg
        w.wg w.ambient (some (entry, consumed)) current after trivial native (entry, consumed) rfl
      have observed : entry.lookup.observed = .ok (entry.lookup.entry, entry.lookup.after) := facts.1.2.1
      have committed : consumed.committed = Campaign2.snapshot current after := facts.2.2.1
      refine ⟨⟨facts.1.1, ?_, facts.1.2.2⟩, facts.2.1, ?_, facts.2.2.2⟩
      · simp [restoreResponseLookupCut, restoreResponseLookupRead, observed, Except.map]
      · simp [ResponseConsumed.committedSnapshot, Campaign2.Product.snapshot, committed]

end Leanux.Proofs.WG.Roaming.Product
