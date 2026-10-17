import Leanux.Proofs.WG.Config.MixedAttributeModel
import Leanux.Proofs.WG.Config.MixedAttributeFrames
import Leanux.Proofs.WG.Config.EndpointSources

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- Normal effects of one actual mixed request. Reset-record failures remain
failures; the timestamp in this postcondition comes from its successful prefix. -/
theorem setDevice_mixed_fwmark_scalars (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer)
    (sock : NlSock) (fixtures : FixtureDevices)
    (peers : d.peerList = [pid]) (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures ∧ selectsDevice g d)
      (fun ret g => ret = (if bad then -EINVAL else 0) ∧ readbackFrame g sock fixtures ∧
        ∃ final reset, g.dev = some final ∧ MixedFwmarkEffect d mark pid p psk interval reset final) := by
  let updated := mixedFwmarkBase d mark
  let tail : WG.M Int := do
    _ ← branch .setDevFwmarkPeerIter false
    _ ← branch .setDevPort false
    _ ← branch .setDevReplacePeers false
    _ ← branch .setDevHasPrivateKey false
    devicePeersSource (scalarDeviceAttrs d key psk interval bad)
  have finish (current : Device) (reset : UInt64)
      (same : current = {updated with peers := current.peers})
      (selected : current.peers[pid]? = some (clearedSource p reset))
      (others : ∀ q, q ≠ pid → current.peers[q]? = d.peers[q]?) :
      Ensures tail (fun g => g.dev = some current ∧ readbackFrame g sock fixtures)
        (fun ret g => ret = (if bad then -EINVAL else 0) ∧ readbackFrame g sock fixtures ∧
          ∃ final reset, g.dev = some final ∧ MixedFwmarkEffect d mark pid p psk interval reset final) := by
    have sameTable := congrArg Device.peerHashtable same
    have sameRunning := congrArg Device.running same
    have hf : current.peerHashtable.find? (·.1 == key) = some (key, pid) := by
      simpa [updated, mixedFwmarkBase] using sameTable ▸ found
    have hd : current.running = false := by simpa [updated, mixedFwmarkBase] using sameRunning.trans down
    have ht := (returns_iff _ _ _).mpr
      (devicePeers_scalars_framed d current key psk interval bad pid (clearedSource p reset)
        sock fixtures hf selected live bounded hd)
    intro g a ret final after pre run
    let start := {a with steps := (((a.steps.push {
      decision := .setDevFwmarkPeerIter, outcome := false, netRx := a.netRxSection}).push {
      decision := .setDevPort, outcome := false, netRx := a.netRxSection}).push {
      decision := .setDevReplacePeers, outcome := false, netRx := a.netRxSection}).push {
      decision := .setDevHasPrivateKey, outcome := false, netRx := a.netRxSection}}
    obtain ⟨value, out, rest, executed, code, device, framed⟩ := ht g start pre
    have source : (tail.run g).run a =
        ((devicePeersSource (scalarDeviceAttrs d key psk interval bad)).run g).run start := by
      simp [tail, branch, AmbientM.branch, start]
    rw [source, executed] at run
    cases run
    refine ⟨code, framed, scalarDevice current pid (clearedSource p reset) psk interval, reset, device, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · have outer := congrArg withoutPeers same
      simpa [scalarDevice, withPeer, withoutPeers, updated] using outer
    · exact scalarDevice_peer current pid (clearedSource p reset) psk interval
    · intro q different
      simpa [scalarDevice, withPeer, Std.TreeMap.getElem?_insert, Ne.symm different] using others q different
  have clear : Ensures (do clearPeerEndpointSrc pid; tail)
      (fun g => g.dev = some updated ∧ readbackFrame g sock fixtures)
      (fun ret g => ret = (if bad then -EINVAL else 0) ∧ readbackFrame g sock fixtures ∧
        ∃ final reset, g.dev = some final ∧ MixedFwmarkEffect d mark pid p psk interval reset final) := by
    refine ensures_bind (Q := fun _ g => ∃ current reset,
      g.dev = some current ∧ current = {updated with peers := current.peers} ∧
      current.peers[pid]? = some (clearedSource p reset) ∧
      (∀ q, q ≠ pid → current.peers[q]? = d.peers[q]?) ∧ readbackFrame g sock fixtures) _ _ ?_ ?_
    · intro g a value out rest pre run
      obtain ⟨current, reset, device, same, selected, others⟩ :=
        clearEndpointSource_exact pid updated p resident g a value out rest pre.1 run
      exact ⟨current, reset, device, same, selected, others,
        clearEndpointSource_readbackFrame pid sock fixtures g a value out rest pre.2 run⟩
    · intro value g a ret final after pre run
      obtain ⟨current, reset, device, same, selected, others, framed⟩ := pre
      exact finish current reset same selected others g a ret final after ⟨device, framed⟩ run
  intro g a ret final after pre run
  obtain ⟨value, middle, next, lookupRun, lookupValue, device, framed⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_framed d sock fixtures) g a pre
  subst value
  let logged (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := logged (logged (logged (logged (logged (logged (logged (logged (logged (logged next
    .setDevLookupErr false) .setDevHasFlags false) .setDevBadFlags false)
    .setDevHasPort false) .setDevHasFwmark true) .setDevNoNet false)
    .setDevNotCapable false) .setDevPermErr false) .setDevFwmark true) .setDevFwmarkPeerIter true
  have source : ((wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)).run g).run a =
      (((do clearPeerEndpointSrc pid; tail) : WG.M Int).run {middle with dev := some updated}).run before := by
    rw [← wgSetDevice_source]
    simp [wgSetDeviceSource, mixedFwmarkAttrs, scalarDeviceAttrs, WG.orM, branch, AmbientM.branch, WGDEVICE_F_ALL]
    rw [show ((lookupInterface (byIndex d)).run g).run a = .ok ((.ok (), middle), next) from lookupRun]
    dsimp only [bind, Except.bind]
    cases cleared : ((clearPeerEndpointSrc pid).run {middle with dev := some updated}).run before
    all_goals have executed := cleared
    all_goals simp only [updated, mixedFwmarkBase, before, logged, net, peers, StateT.run] at executed
    all_goals simp [deviceUpdateSource, deviceKeySource, WG.andM, branch, AmbientM.branch,
      getDev, device, net, modifyDev, peers, WGDEVICE_F_REPLACE_PEERS,
      List.forIn_cons, List.forIn_nil, tail,
      scalarDeviceAttrs, StateT.run, StateT.bind, StateT.lift, StateT.pure, Except.bind, Except.pure,
      liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
      MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get, Functor.map, StateT.map, executed]
    all_goals rfl
  exact clear {middle with dev := some updated} before ret final after ⟨rfl, framed⟩ (source.symm.trans run)

end Leanux.Proofs.WG.Config
