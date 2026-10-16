import Leanux.Proofs.WG.AllowedIps.RoutingCompletions

/-! Actual public-key-table acquisition and creation establish routing residency.
The returned slot is not asserted to match a peer's cryptographic identity. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem pubkeyLookup_borrowed_spec (key : Key) (initial : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ pubkeyLookup key
    ⦃⇓? result w => ⌜PeerBorrow.Borrowed initial result (wgStoreView w)⌝⦄ := by
  have ha := fun peer => PeerBorrow.acquire_spec peer initial
  mvcgen [pubkeyLookup, ha, getDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals simp_all

theorem pubkeyLookup_routed (key : Key)
    (hr : ((pubkeyLookup key).run w).run ambient = .ok ((result, v), ambient')) :
    routingView v = routingView w ∧
      ∀ pid, result = some pid → RoutingResident pid (routingView v) := by
  have hb := (hoare_iff_run_ambient _ _ _).mp (pubkeyLookup_borrowed_spec key (wgStoreView w))
    w ambient result v ambient' rfl hr
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at hb
    have hd := congrArg WGStoreView.dev hb
    change v.dev = w.dev at hd
    simp [routingView, hd]
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    have hv := congrArg WGStoreView.dev hk
    change v.dev = some { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } } at hv
    change w.dev = some d at hd
    have hs := routingState_insert_same d pid p {p with refcount := p.refcount + 1} hp rfl
    refine ⟨by simp [routingView, hv, hd, hs], ?_⟩
    intro q hq
    cases hq
    exact routingResident_of_peer (d := {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}})
      (p := {p with refcount := p.refcount + 1}) hv (by simp)

def CompletionAcquired (initial : FlatTable × FlatTable) (peer : Option PeerId)
    (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  CompletionState initial h w ∧ ∀ pid, peer = some pid → RoutingResident pid (routingView w)

theorem pubkeyLookup_completion (initial : FlatTable × FlatTable) (key : Key) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (liftWGPrefix (pubkeyLookup key)) (fun result h w _ => CompletionAcquired initial result h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient result v ambient' hi hr
  have hf := pubkeyLookup_routed key hr
  exact ⟨⟨hi.1, hf.1 ▸ hi.2⟩, hf.2⟩

def CompletionCreated (initial : FlatTable × FlatTable) (result : Except Int PeerId)
    (h : List RoutingCompletion) (w : WGWorld) : Prop :=
  match result with
  | .error _ => CompletionState initial h w
  | .ok pid => CompletionTarget initial pid h w

theorem peerCreate_completion (initial : FlatTable × FlatTable) (key : Key) (psk : Option Key) :
    StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (liftWGPrefix (peerCreate key psk)) (fun result h w _ => CompletionCreated initial result h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient result v ambient' hi hr
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.2.realize
  have step : RoutingStep w ambient (.create key psk result) v ambient' := .create hr
  obtain ⟨out, u4, u6, hout, ho, he4, he6⟩ := step.refines hd hinv h4 h6
  have state : CompletionState initial h v :=
    ⟨hi.1, out, u4, u6, by simp [routingView, hout], ho, he4, he6⟩
  cases result with
  | error err => exact state
  | ok pid =>
    have hc := peerCreate_routing w v ambient ambient' key psk (.ok pid) hr
    obtain ⟨s, _, hpid, he⟩ := hc
    refine ⟨state, s.allocate, [], he, ?_⟩
    simp [RoutingState.allocate, hpid]

end Leanux.Proofs.WG.AllowedIps
