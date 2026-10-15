import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Roaming.PublicationFrames
import Leanux.Proofs.WG.Config.PeerScalars

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The actual successful public-key lookup derives its first table match and
reference acquisition. No peer public-key coherence premise is supplied. -/
theorem initiation_pubkey_provenance (key : Key) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ pubkeyLookup key
      ⦃⇓? ret w => ⌜∀ pid, ret = some pid → ∃ d p,
        initial.wg = some d ∧
        d.peerHashtable.find? (·.1 == key) = some (key, pid) ∧
        d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2^31 ∧
        w.k.wg = some (withPeer d pid { p with refcount := p.refcount + 1 })⌝⦄ := by
  mvcgen [pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
    branch, branchCmp, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [-List.find?_eq_none, withPeer]
  all_goals grind

def initiationLookup (key : Key) : M InitiationLookup := do
  let before ← Campaign2.read
  let observed ← Campaign2.inspect (pubkeyLookup key)
  let result ← pubkeyLookup key
  let after ← Campaign2.read
  return ⟨before, observed, result, after⟩

/-- The inspection and the actual lookup have the same entry state. -/
theorem initiationLookup_bind {α : Type} (key : Key) (next : Option PeerId → M α) :
    (initiationLookup key >>= fun out => next out.result) = (pubkeyLookup key >>= next) := by
  funext entry
  change (((pubkeyLookup key).run entry >>= fun pair =>
    Except.ok (InitiationLookup.mk (Campaign2.snapshot entry)
      (Campaign2.observeResult ((pubkeyLookup key).run entry)) pair.1
      (Campaign2.snapshot pair.2), pair.2)) >>= fun out => next out.1.result out.2) =
    ((pubkeyLookup key).run entry >>= fun out => next out.1 out.2)
  cases run : (pubkeyLookup key).run entry <;> rfl

theorem initiationLookup_facts (key : Key) :
    Ensures (initiationLookup key) (fun _ => True)
      (fun out _ => ∀ pid, out.result = some pid → InitiationLookupFacts key pid out) := by
  intro entry out final pre run
  change ((pubkeyLookup key).run entry >>= fun pair =>
    Except.ok (InitiationLookup.mk (Campaign2.snapshot entry)
      (Campaign2.observeResult ((pubkeyLookup key).run entry)) pair.1
      (Campaign2.snapshot pair.2), pair.2)) = .ok (out, final) at run
  cases lookup : (pubkeyLookup key).run entry with
  | error err => rw [lookup] at run; cases run
  | ok pair =>
    rcases pair with ⟨result, after⟩
    rw [lookup] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    intro pid selected
    have facts := (ensures_iff _ _ _).mpr (initiation_pubkey_provenance key entry.k)
      entry result after rfl lookup pid selected
    change result = some pid at selected
    subst result
    exact ⟨rfl, rfl, facts⟩

end Leanux.Proofs.WG.Roaming
