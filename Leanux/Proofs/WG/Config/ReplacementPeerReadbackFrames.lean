import Leanux.Proofs.WG.Config.AllowedRemovalReadbackFrames
import Leanux.Proofs.WG.Config.ReplacementConverseSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The replacement update preserves the getter socket and fixture selector on
normal return. Its actual removal prefix supplies the retained peer for cleanup. -/
theorem replacementUpdate_readbackFrame (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (sock : NlSock) (fixtures : FixtureDevices)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (retained : 1 < p.refcount) (down : d.running = false) :
    Ensures (peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
      WGPEER_F_REPLACE_ALLOWEDIPS none pid)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
  have tail (entry : Device) (q : Peer) (peer : entry.peers[pid]? = some q)
      (refs : 1 < q.refcount) (stopped : entry.running = false) :
      Ensures (peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid)
        (fun g => g.dev = some entry ∧ readbackFrame g sock fixtures)
        (fun _ g => readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}}
    let before := mark (mark (mark (mark ambient .peerHasAips true)
      .peerAipsIter false) .peerHasKeepalive false) .peerRunning false
    obtain ⟨done, out, middle, putRun, _, frame⟩ :=
      (returns_iff _ _ _).mpr (peerPut_retained_returns_framed sock fixtures pid entry q peer refs)
        g before pre
    cases done
    have source : ((peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid).run g).run ambient =
        .ok ((0, out), mark middle .peerZeroPsk false) := by
      simp [peerConfigTailSource, replaceAllowedipsAttrs, branch, AmbientM.branch,
        List.forIn_nil, getDev, pre.1, stopped]
      rw [show ((peerPut (some pid)).run g).run before = .ok (((), out), middle) from putRun]
      rfl
    rw [source] at run
    cases run
    exact frame
  have removal : Ensures (removeByPeer pid)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => ∃ removed, g.dev = some removed ∧ RemovalEffect d p.allowedipsList removed ∧
        readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    obtain ⟨removed, device, steps⟩ := removeByPeer_effect_pairs pid d p resident pairs
      g ambient result final after pre.1 run
    exact ⟨removed, device, steps,
      removeByPeer_readbackFrame pid sock fixtures g ambient result final after pre.2 run⟩
  have body : Ensures (do
      removeByPeer pid
      peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
    refine ensures_bind _ _ removal ?_
    intro u g ambient result final after pre run
    obtain ⟨removed, device, steps, frame⟩ := pre
    let q := erasePeerList p.allowedipsList p
    have peer : removed.peers[pid]? = some q := by
      simpa [resident, q] using removalEffect_peers steps pid
    have refs : q.refcount = p.refcount := erasePeerList_refcount _ _
    exact tail removed q peer (by rwa [refs]) ((removalEffect_running steps).trans down)
      g ambient result final after ⟨device, frame⟩ run
  intro g ambient result final after pre run
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark ambient .peerRemoveMe false)
    .peerSetPsk false) .peerHasEndpoint false) .peerReplaceAips true
  have source : ((peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
      WGPEER_F_REPLACE_ALLOWEDIPS none pid).run g).run ambient =
      (((do removeByPeer pid
            peerConfigTailSource (replaceAllowedipsAttrs key) (some pid) pid) : WG.M Int).run g).run before := by
    have removeOff : (2 : UInt32) &&& 1 = 0 := by decide
    simp [peerConfigUpdateSource, replaceAllowedipsAttrs, WGPEER_F_REPLACE_ALLOWEDIPS,
      WGPEER_F_REMOVE_ME, branch, AmbientM.branch, removeOff, before, mark]
  exact body g before result final after pre (source.symm.trans run)

/-- The actual lookup, acquired reference, and replacement update preserve the
readback fields. Removal failures remain outside this normal-return contract. -/
theorem setPeer_replace_readbackFrame (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (setPeerCmd (replaceAllowedipsAttrs key))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
  intro g ambient result final after pre run
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark (mark (mark ambient
    .peerHasPubkey true) .peerPubkeyLen true) .peerHasPsk false)
    .peerHasFlags true) .peerBadFlags false) .peerHasProtocol false
  let acquired := {p with refcount := p.refcount + 1}
  let acquiredDevice := withPeer d pid acquired
  obtain ⟨got, middle, a1, lookupRun, value, acquiredState, frame⟩ :=
    (returns_iff _ _ _).mpr (pubkeyLookup_present_returns_framed sock fixtures key pid d p
      found resident live bounded) g before pre
  subst got
  have source : ((setPeerCmd (replaceAllowedipsAttrs key)).run g).run ambient =
      ((peerConfigUpdateSource (replaceAllowedipsAttrs key) (some pid)
        WGPEER_F_REPLACE_ALLOWEDIPS none pid).run middle).run (mark a1 .peerNotFound false) := by
    have good : (2 : UInt32) &&& ~~~7 = 0 := by decide
    rw [← setPeerCmd_source]
    simp [setPeerCmdSource, replaceAllowedipsAttrs, WGPEER_F_ALL, WGPEER_F_REPLACE_ALLOWEDIPS,
      WG.andM, branch, AmbientM.branch, good]
    rw [show ((pubkeyLookup key).run g).run before = .ok ((some pid, middle), a1) from lookupRun]
    rfl
  exact replacementUpdate_readbackFrame key pid acquiredDevice acquired sock fixtures
    (by simp [acquiredDevice, withPeer]) pairs (by simpa [acquired] using live) down
    middle (mark a1 .peerNotFound false) result final after ⟨acquiredState, frame⟩ (source.symm.trans run)

end Leanux.Proofs.WG.Config
