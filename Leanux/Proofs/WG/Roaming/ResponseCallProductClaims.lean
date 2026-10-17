import Leanux.Proofs.WG.Roaming.ResponseCallClaims
import Leanux.Proofs.WG.Roaming.ResponseCallProductSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

theorem responsePacketPrefix_facts (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Campaign2.Product.Ensures (responsePacketPrefix msg src underLoad) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        cut.beforeSetter = s ∧ ResponseCallFacts msg cut) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [responsePacketPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.responsePacketPrefix msg src underLoad).run w.wg).run w.ambient with
  | error stop => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, current⟩, after⟩
    simp only [StateT.run] at native
    rw [native] at run
    cases value with
    | none => cases run
    | some value =>
      simp only [Option.map_some, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      have facts := Roaming.responsePacketPrefix_facts msg src underLoad
        w.wg w.ambient (some value) current after trivial native value rfl
      constructor
      · simp [restoreResponseCallCut, Campaign2.Product.snapshot, facts.1]
      · rcases facts.2 with ⟨mac, lookup, sameInput, consumed, device⟩
        refine ⟨mac, ⟨lookup.1, ?_, lookup.2.2⟩, sameInput, consumed, device⟩
        simp [restoreResponseCallCut, restoreResponseLookupCut, restoreResponseLookupRead,
          lookup.2.1, Except.map]

theorem responseCallPrefix_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Product.Ensures (responseCallPrefix msg src) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        cut.beforeSetter = s ∧ ResponseCallFacts msg cut) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [responseCallPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.responseCallPrefix msg src).run w.wg).run w.ambient with
  | error stop => simp only [StateT.run] at native; rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, current⟩, after⟩
    simp only [StateT.run] at native
    rw [native] at run
    cases value with
    | none => cases run
    | some value =>
      simp only [Option.map_some, Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      have facts := Roaming.responseCallPrefix_facts msg src
        w.wg w.ambient (some value) current after trivial native value rfl
      constructor
      · simp [restoreResponseCallCut, Campaign2.Product.snapshot, facts.1]
      · rcases facts.2 with ⟨mac, lookup, sameInput, consumed, device⟩
        refine ⟨mac, ⟨lookup.1, ?_, lookup.2.2⟩, sameInput, consumed, device⟩
        simp [restoreResponseCallCut, restoreResponseLookupCut, restoreResponseLookupRead,
          lookup.2.1, Except.map]

theorem observedResponseHandshake_facts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.Ensures (observedResponseHandshake msg src) (fun _ => True)
      (fun observed _ => ResponseCallObservation msg observed) := by
  intro w observed final _ run
  rw [observedResponseHandshake_source msg src kind] at run
  change ((responseCallPrefix msg src).run w >>= fun (candidate, atCut) =>
    (responseCallSuffix msg src candidate).run atCut >>= fun (_, finish) =>
      Except.ok (Except.ok (candidate, Campaign2.Product.snapshot atCut), finish)) = _ at run
  cases prefixRun : (responseCallPrefix msg src).run w with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    rw [prefixRun] at run
    change ((responseCallSuffix msg src candidate).run atCut >>= fun (_, finish) =>
      Except.ok (Except.ok (candidate, Campaign2.Product.snapshot atCut), finish)) = _ at run
    cases suffixRun : (responseCallSuffix msg src candidate).run atCut with
    | error stop => rw [suffixRun] at run; cases run
    | ok pair =>
      rcases pair with ⟨value, finish⟩
      rw [suffixRun] at run
      cases run
      exact ⟨candidate, Campaign2.Product.snapshot atCut, rfl,
        responseCallPrefix_facts msg src w candidate atCut trivial prefixRun⟩

end Leanux.Proofs.WG.Roaming.Product
