import Leanux.Proofs.WG.Roaming.InitiationCallClaims
import Leanux.Proofs.WG.Roaming.InitiationCallProductSource
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

theorem initiationPacketPrefix_facts (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Campaign2.Product.Ensures (initiationPacketPrefix msg src underLoad) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        cut.beforeSetter = s ∧ InitiationCallFacts msg cut) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [initiationPacketPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.initiationPacketPrefix msg src underLoad).run w.wg).run w.ambient with
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
      have facts := Roaming.initiationPacketPrefix_facts msg src underLoad
        w.wg w.ambient (some value) current after trivial native value rfl
      constructor
      · simp [restoreInitiationCallCut, Campaign2.Product.snapshot, facts.1]
      · rcases facts.2 with ⟨mac, consumed, device⟩
        rcases consumed with ⟨identity, dh, decrypted, lookup, peer, nonzero, timestamp, commit⟩
        refine ⟨mac, ⟨identity, dh, decrypted, ⟨lookup.1, ?_, lookup.2.2⟩,
          peer, nonzero, timestamp, commit⟩, device⟩
        simp [restoreInitiationCallCut, restoreInitiationConsume, restoreInitiationFinish,
          restoreInitiationLookup, lookup.2.1, Except.map]

theorem initiationCallPrefix_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Product.Ensures (initiationCallPrefix msg src) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        cut.beforeSetter = s ∧ InitiationCallFacts msg cut) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [initiationCallPrefix, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.initiationCallPrefix msg src).run w.wg).run w.ambient with
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
      have facts := Roaming.initiationCallPrefix_facts msg src
        w.wg w.ambient (some value) current after trivial native value rfl
      constructor
      · simp [restoreInitiationCallCut, Campaign2.Product.snapshot, facts.1]
      · rcases facts.2 with ⟨mac, consumed, device⟩
        rcases consumed with ⟨identity, dh, decrypted, lookup, peer, nonzero, timestamp, commit⟩
        refine ⟨mac, ⟨identity, dh, decrypted, ⟨lookup.1, ?_, lookup.2.2⟩,
          peer, nonzero, timestamp, commit⟩, device⟩
        simp [restoreInitiationCallCut, restoreInitiationConsume, restoreInitiationFinish,
          restoreInitiationLookup, lookup.2.1, Except.map]

theorem observedInitiationHandshake_facts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.Product.Ensures (observedInitiationHandshake msg src) (fun _ => True)
      (fun observed _ => InitiationCallObservation msg observed) := by
  intro w observed final _ run
  rw [observedInitiationHandshake_source msg src kind] at run
  change ((initiationCallPrefix msg src).run w >>= fun (candidate, atCut) =>
    (initiationCallSuffix msg src candidate).run atCut >>= fun (_, finish) =>
      Except.ok (Except.ok (candidate, Campaign2.Product.snapshot atCut), finish)) = _ at run
  cases prefixRun : (initiationCallPrefix msg src).run w with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    rw [prefixRun] at run
    change ((initiationCallSuffix msg src candidate).run atCut >>= fun (_, finish) =>
      Except.ok (Except.ok (candidate, Campaign2.Product.snapshot atCut), finish)) = _ at run
    cases suffixRun : (initiationCallSuffix msg src candidate).run atCut with
    | error stop => rw [suffixRun] at run; cases run
    | ok pair =>
      rcases pair with ⟨value, finish⟩
      rw [suffixRun] at run
      cases run
      exact ⟨candidate, Campaign2.Product.snapshot atCut, rfl,
        initiationCallPrefix_facts msg src w candidate atCut trivial prefixRun⟩

end Leanux.Proofs.WG.Roaming.Product
