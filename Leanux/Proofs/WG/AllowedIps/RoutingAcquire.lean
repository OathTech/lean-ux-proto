import Leanux.Proofs.WG.AllowedIps.RoutingCompletions
import Leanux.Proofs.WG.AllowedIps.RoutingSendFrames

/-! Actual public-key-table acquisition and creation establish routing residency.
The returned slot is not asserted to match a peer's cryptographic identity. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem pubkeyLookup_borrowed_spec (key : Key) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ pubkeyLookup key
    ⦃⇓? result w => ⌜PeerBorrow.Borrowed initial result w.k⌝⦄ := by
  have ha := fun peer => PeerBorrow.acquire_spec peer initial
  mvcgen [pubkeyLookup, ha, getDev, getK, branch, invariant]
  all_goals simp_all

theorem pubkeyLookup_routed (key : Key)
    (hr : (pubkeyLookup key).run w = .ok (result, v)) :
    routingView v = routingView w ∧
      ∀ pid, result = some pid → RoutingResident pid (routingView v) := by
  have hb := (hoare_iff_triple _ _ _).mpr (pubkeyLookup_borrowed_spec key w.k) w result v rfl hr
  cases result with
  | none =>
    change v.k = w.k at hb
    simp [routingView, hb]
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    have hs := routingState_insert_same d pid p {p with refcount := p.refcount + 1} hp rfl
    refine ⟨by simp [routingView, hk, hd, hs], ?_⟩
    intro q hq
    cases hq
    exact routingResident_of_peer (d := {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}})
      (p := {p with refcount := p.refcount + 1}) (by rw [hk]) (by simp)

def CompletionAcquired (initial : FlatTable × FlatTable) (peer : Option PeerId)
    (h : List RoutingCompletion) (w : World) : Prop :=
  CompletionState initial h w ∧ ∀ pid, peer = some pid → RoutingResident pid (routingView w)

theorem pubkeyLookup_completion (initial : FlatTable × FlatTable) (key : Key) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial) (liftPrefix (pubkeyLookup key))
      (CompletionAcquired initial) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w result v hi hr
  have hf := pubkeyLookup_routed key hr
  exact ⟨⟨hi.1, hf.1 ▸ hi.2⟩, hf.2⟩

def CompletionCreated (initial : FlatTable × FlatTable) (result : Except Int PeerId)
    (h : List RoutingCompletion) (w : World) : Prop :=
  match result with
  | .error _ => CompletionState initial h w
  | .ok pid => CompletionTarget initial pid h w

theorem peerCreate_completion (initial : FlatTable × FlatTable) (key : Key) (psk : Option Key) :
    PrefixEnsures (CompletionState initial) (CompletionSafe initial) (liftPrefix (peerCreate key psk))
      (CompletionCreated initial) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w result v hi hr
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.2.realize
  have step : RoutingStep w (.create key psk result) v := .create hr
  obtain ⟨out, u4, u6, hout, ho, he4, he6⟩ := step.refines hd hinv h4 h6
  have state : CompletionState initial h v :=
    ⟨hi.1, out, u4, u6, by simp [routingView, hout], ho, he4, he6⟩
  cases result with
  | error err => exact state
  | ok pid =>
    have hc := peerCreate_routing w v key psk (.ok pid) hr
    obtain ⟨s, _, hpid, he⟩ := hc
    refine ⟨state, s.allocate, [], he, ?_⟩
    simp [RoutingState.allocate, hpid]

end Leanux.Proofs.WG.AllowedIps
