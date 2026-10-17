import Leanux.Proofs.WG.Roaming.InitiationConsumeSource
import Leanux.Proofs.WG.Roaming.InitiationConsumeProductModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

def initiationFinish (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Product.Snapshot)
    (ck timestamp hash : List UInt8) : Leanux.M (Option InitiationConsumed) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.initiationFinish msg identity s pid (nativeInitiationLookup lookup)
    dhPeer beforeDh.toSnapshot ck timestamp hash)
  pure (out.map (restoreInitiationFinish fixture lookup beforeDh))

theorem initiationFinish_facts (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Product.Snapshot)
    (ck timestamp hash : List UInt8) :
    Campaign2.Product.Ensures (initiationFinish msg identity s pid lookup dhPeer beforeDh ck timestamp hash)
      (fun _ => True)
      (fun result observed => ∀ cut, result = some cut →
        cut.committed = observed ∧ cut.identity = identity ∧ cut.staticPlain = s ∧
        cut.timestamp = timestamp ∧ cut.pid = pid ∧ cut.lookup = lookup ∧
        cut.dhPeer = dhPeer ∧ cut.beforeDh = beforeDh ∧ InitiationCommitFacts msg ck hash cut) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [initiationFinish, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.initiationFinish msg identity s pid (nativeInitiationLookup lookup)
      dhPeer beforeDh.toSnapshot ck timestamp hash).run w.wg).run w.ambient with
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
      rcases Roaming.initiationFinish_facts msg identity s pid (nativeInitiationLookup lookup)
        dhPeer beforeDh.toSnapshot ck timestamp hash w.wg w.ambient (some value) current after
        trivial native value rfl with
          ⟨committed, identityEq, staticEq, timestampEq, pidEq, _, dhEq, _, commitFacts⟩
      refine ⟨?_, identityEq, staticEq, timestampEq, pidEq, rfl, dhEq, rfl, commitFacts⟩
      simp [restoreInitiationFinish, Campaign2.Product.snapshot, committed]


/-- Execute the native consumer once and retain its actual product observations. -/
def initiationConsume (msg : List UInt8) : Leanux.M (Option InitiationConsumed) := do
  let fixture := (← Campaign2.Product.read).fixture
  let out ← liftWG (Roaming.initiationConsume msg)
  pure (out.map (restoreInitiationConsume fixture))

def initiationPeer (out : Option InitiationConsumed) : Option PeerId := out.map (·.pid)

theorem initiationConsume_erase (msg : List UInt8) :
    (do let out ← initiationConsume msg; pure (initiationPeer out)) =
      liftWG (consumeInitiation msg) := by
  rw [← Roaming.initiationConsume_erase]
  funext w
  dsimp only [initiationConsume, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((Roaming.initiationConsume msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨out, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]
    cases out <;> rfl

theorem initiationConsume_facts (msg : List UInt8) :
    Campaign2.Product.Ensures (initiationConsume msg) (fun _ => True)
      (fun result observed => ∀ cut, result = some cut →
        cut.committed = observed ∧ InitiationConsumedFacts msg cut) := by
  intro w result final _ run cut returned
  subst result
  dsimp only [initiationConsume, Campaign2.Product.read, liftWG, StateT.run,
    StateT.bind, StateT.pure, StateT.map, Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure] at run
  cases native : ((Roaming.initiationConsume msg).run w.wg).run w.ambient with
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
      obtain ⟨committed, identity, dh, decrypted, lookup, peer, nonzero, timestamp, facts⟩ :=
        Roaming.initiationConsume_facts msg w.wg w.ambient (some value) current after
          trivial native value rfl
      refine ⟨?_, identity, dh, decrypted, ?_, peer, nonzero, timestamp, facts⟩
      · simp [restoreInitiationConsume, restoreInitiationFinish, Campaign2.Product.snapshot, committed]
      · rcases lookup with ⟨selected, observed, provenance⟩
        refine ⟨selected, ?_, provenance⟩
        simp [restoreInitiationConsume, restoreInitiationFinish, restoreInitiationLookup, observed]
        rfl

end Leanux.Proofs.WG.Roaming.Product
