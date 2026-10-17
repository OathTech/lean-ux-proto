import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Config.PeerScalars

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- The successful lookup derives the first matching table entry and reference
acquisition from the projected initial device, with no coherence assumption. -/
theorem initiation_pubkey_provenance (key : Key) (initial : Campaign2.Snapshot) :
    Campaign2.Ensures (pubkeyLookup key) (fun s => s.wg.device = initial.wg.device)
      (fun ret s => ∀ pid, ret = some pid → ∃ d p,
        initial.wg.device = some d ∧
        d.peerHashtable.find? (·.1 == key) = some (key, pid) ∧
        d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2^31 ∧
        s.wg.device = some (withPeer d pid { p with refcount := p.refcount + 1 })) := by
  intro g ambient ret final after pre run pid selected
  subst ret
  change g.dev = initial.wg.device at pre
  cases device : g.dev with
  | none =>
    simp [pubkeyLookup, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.peerHashtable.find? (·.1 == key) with
    | none =>
      simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero,
        branch, AmbientM.branch] at run
      cases run
    | some pair =>
      rcases pair with ⟨tableKey, target⟩
      have same : tableKey = key := by simpa using List.find?_some found
      subst tableKey
      cases resident : d.peers[target]? with
      | none =>
        simp [pubkeyLookup, getDev, device, found, peerGetMaybeZero, requireNotPending,
          getPeer, resident, branch, AmbientM.branch, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
            getDev, device, found, getPeer, resident, zero, branch, branchCmp,
            AmbientM.branch, AmbientM.branchCmp] at run
          cases run
        · by_cases overflow : 2147483647 ≤ p.refcount
          · simp [pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
              getDev, device, found, getPeer, resident, zero, overflow, branch, branchCmp,
              AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported] at run
            cases run
          · simp [pubkeyLookup, peerGetMaybeZero, requireNotPending, refcountIncNotZero,
              getDev, device, found, getPeer, resident, zero, overflow, branch, branchCmp,
              AmbientM.branch, AmbientM.branchCmp, setPeer, modifyDev] at run
            rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
            exact ⟨d, p, pre.symm.trans device, found, resident, by omega, by omega, rfl⟩

def initiationLookup (key : Key) : WG.M InitiationLookup := do
  let before ← Campaign2.read
  let observed ← Campaign2.inspect (pubkeyLookup key)
  let result ← pubkeyLookup key
  let after ← Campaign2.read
  return ⟨before, observed, result, after⟩

/-- Native continuations receive the actual two successor states. -/
theorem initiationLookup_bind {α : Type} (key : Key) (next : Option PeerId → WG.M α) :
    (initiationLookup key >>= fun out => next out.result) = (pubkeyLookup key >>= next) := by
  funext g ambient
  change ((((pubkeyLookup key).run g).run ambient >>= fun ((result, current), after) =>
    Except.ok ((InitiationLookup.mk (Campaign2.snapshot g ambient)
      (Campaign2.observeResult (((pubkeyLookup key).run g).run ambient)) result
      (Campaign2.snapshot current after), current), after)) >>= fun ((out, current), after) =>
        ((next out.result).run current).run after) =
    (((pubkeyLookup key).run g).run ambient >>= fun ((result, current), after) =>
      ((next result).run current).run after)
  cases run : ((pubkeyLookup key).run g).run ambient with
  | error err => rfl
  | ok pair => rcases pair with ⟨⟨result, current⟩, after⟩; rfl

theorem initiationLookup_facts (key : Key) :
    Campaign2.Ensures (initiationLookup key) (fun _ => True)
      (fun out _ => ∀ pid, out.result = some pid → InitiationLookupFacts key pid out) := by
  intro g ambient out final after _ run
  change (((pubkeyLookup key).run g).run ambient >>= fun ((result, current), last) =>
    Except.ok ((InitiationLookup.mk (Campaign2.snapshot g ambient)
      (Campaign2.observeResult (((pubkeyLookup key).run g).run ambient)) result
      (Campaign2.snapshot current last), current), last)) = .ok ((out, final), after) at run
  cases lookup : ((pubkeyLookup key).run g).run ambient with
  | error err => rw [lookup] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨result, current⟩, last⟩
    rw [lookup] at run
    cases run
    intro pid selected
    have facts := initiation_pubkey_provenance key (Campaign2.snapshot g ambient)
      g ambient result final after rfl lookup pid selected
    change result = some pid at selected
    subst result
    exact ⟨rfl, rfl, facts⟩

end Leanux.Proofs.WG.Roaming
