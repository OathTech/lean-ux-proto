import Leanux.Proofs.WG.Config.KeyPeerEffects
import Leanux.Proofs.WG.Config.KeyInstall

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem keyPeer_missing_full (pid : PeerId) (sendStaged : Bool) :
    Ensures (keyPeerSource pid sendStaged) (fun g => peerAt g pid = none) (fun _ _ => False) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [keyPeerSource, precomputeStaticStatic, requireNotPending, getDev, device,
      invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have missing : d.peers[pid]? = none := by simpa [peerAt, device] using pre
    simp [keyPeerSource, precomputeStaticStatic, requireNotPending, getPeer, getDev, device,
      missing, invariant, AmbientM.invariant] at run
    cases run

/-- The next step is selected by the actual recorded fallback observation. -/
theorem keyPeer_full_step (pid : PeerId) (d : Device) (sendStaged : Bool) :
    Campaign2.Ensures (observedKeyPeerSource pid sendStaged)
      (fun s => s.wg.device = some d)
      (fun observation s => ∃ p, d.peers[pid]? = some p ∧
        keyPeerObservation d pid p sendStaged observation s) := by
  intro g ambient observation final after device run
  change g.dev = some d at device
  cases resident : d.peers[pid]? with
  | none =>
    simp [observedKeyPeerSource, precomputeStaticStatic, requireNotPending,
      getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
    cases run
  | some p =>
    exact ⟨p, rfl, keyPeer_complete pid d p sendStaged resident
      g ambient observation final after device run⟩

private theorem keyPeerObservation_device (d : Device) (pid : PeerId) (p : Peer)
    (sendStaged : Bool) (observation : Option (Int64 × Option Bool)) (s : Campaign2.Snapshot)
    (effect : keyPeerObservation d pid p sendStaged observation s) :
    ∃ next, s.wg.device = some next := by
  obtain ⟨now, effect⟩ := effect
  cases sendStaged with
  | false => exact ⟨_, effect.2⟩
  | true =>
    simp only [↓reduceIte] at effect
    unfold invalidStagedObservation at effect
    split at effect
    · exact ⟨_, effect.2⟩
    · obtain ⟨observed, _, effect⟩ := effect
      unfold stagedFallbackObservation at effect
      split at effect
      · exact ⟨_, effect.1⟩
      · exact ⟨_, effect.2.2⟩

/-- Historical ordered Device relation retained for pending downstream carries.
Its queued-send prediction does not describe the current source; the checked
contracts below use ObservedKeyPeerRun and actual fallback observations. -/
inductive KeyPeerRun (sendStaged : Bool) : Device → List PeerId → Device → Prop
  | nil (d : Device) : KeyPeerRun sendStaged d [] d
  | cons (d : Device) (pid : PeerId) (p : Peer) (expiryNow queueNow : Int64)
      (rest : List PeerId) (final : Device)
      (resident : d.peers[pid]? = some p)
      (tail : KeyPeerRun sendStaged (keyPeerDevice d pid p expiryNow sendStaged queueNow) rest final) :
      KeyPeerRun sendStaged d (pid :: rest) final

/-- The witnesses are projections of the actual intermediate runs supplied by
`keyPeerLoop_complete`; no execution state is realized from a snapshot. -/
inductive ObservedKeyPeerRun (sendStaged : Bool) :
    Device → List PeerId → List (Option (Int64 × Option Bool)) → Device → Prop
  | nil (d : Device) : ObservedKeyPeerRun sendStaged d [] [] d
  | cons (d : Device) (pid : PeerId) (p : Peer) (observation : Option (Int64 × Option Bool))
      (step : Campaign2.Snapshot) (next : Device) (rest : List PeerId)
      (observations : List (Option (Int64 × Option Bool))) (final : Device)
      (resident : d.peers[pid]? = some p)
      (effect : keyPeerObservation d pid p sendStaged observation step)
      (device : step.wg.device = some next)
      (tail : ObservedKeyPeerRun sendStaged next rest observations final) :
      ObservedKeyPeerRun sendStaged d (pid :: rest) (observation :: observations) final

def observedKeyPeerLoopSource (pids : List PeerId) (sendStaged : Bool) :
    WG.M (List (Option (Int64 × Option Bool))) :=
  match pids with
  | [] => pure []
  | pid :: rest => do
    _ ← branch .setDevKeyPeerIter true
    let observation ← observedKeyPeerSource pid sendStaged
    let tail ← observedKeyPeerLoopSource rest sendStaged
    pure (observation :: tail)

theorem keyPeerLoop_complete (pids : List PeerId) (d : Device) (sendStaged : Bool) :
    Campaign2.Ensures (observedKeyPeerLoopSource pids sendStaged)
      (fun s => s.wg.device = some d)
      (fun observations s => ∃ final, s.wg.device = some final ∧
        ObservedKeyPeerRun sendStaged d pids observations final) := by
  induction pids generalizing d with
  | nil =>
    intro g ambient observations final after device run
    simp [observedKeyPeerLoopSource] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨d, device, .nil d⟩
  | cons pid rest ih =>
    intro g ambient observations final after device run
    let marked : Ambient := {ambient with steps := ambient.steps.push {decision := .setDevKeyPeerIter, outcome := true, netRx := ambient.netRxSection}}
    change (((observedKeyPeerSource pid sendStaged).run g).run marked >>= _) = _ at run
    cases headRun : ((observedKeyPeerSource pid sendStaged).run g).run marked with
    | error error => rw [headRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨observation, current⟩, inputs⟩ := pair
      obtain ⟨p, resident, effect⟩ := keyPeer_full_step pid d sendStaged
        g marked observation current inputs device headRun
      obtain ⟨next, nextDevice⟩ := keyPeerObservation_device d pid p sendStaged observation
        (Campaign2.snapshot current inputs) effect
      rw [headRun] at run
      change (((observedKeyPeerLoopSource rest sendStaged).run current).run inputs >>= _) = _ at run
      cases tailRun : ((observedKeyPeerLoopSource rest sendStaged).run current).run inputs with
      | error error => rw [tailRun] at run; cases run
      | ok pair =>
        obtain ⟨⟨tail, out⟩, ending⟩ := pair
        rw [tailRun] at run
        cases run
        obtain ⟨done, finalDevice, relation⟩ := ih next current inputs tail final after nextDevice tailRun
        exact ⟨done, finalDevice, .cons d pid p observation (Campaign2.snapshot current inputs)
          next rest tail done resident effect nextDevice relation⟩

private theorem observedKeyPeerSource_erase_device (pid : PeerId) (d : Device)
    (sendStaged : Bool) (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    (((do let _ ← observedKeyPeerSource pid sendStaged; pure ()) : WG.M Unit).run g).run ambient =
      ((keyPeerSource pid sendStaged).run g).run ambient := by
  cases resident : d.peers[pid]? with
  | none =>
    simp [observedKeyPeerSource, keyPeerSource, precomputeStaticStatic, requireNotPending,
      getPeer, getDev, device, resident, invariant, AmbientM.invariant]
    rfl
  | some p => exact observedKeyPeerSource_erase pid d p sendStaged resident g ambient device

theorem observedKeyPeerLoopSource_erase (pids : List PeerId) (d : Device) (sendStaged : Bool)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    (((do let _ ← observedKeyPeerLoopSource pids sendStaged; pure ()) : WG.M Unit).run g).run ambient =
      ((keyPeerLoopSource pids sendStaged).run g).run ambient := by
  induction pids generalizing d g ambient with
  | nil => rfl
  | cons pid rest ih =>
    let marked : Ambient := {ambient with steps := ambient.steps.push {decision := .setDevKeyPeerIter, outcome := true, netRx := ambient.netRxSection}}
    have factor : keyPeerLoopSource (pid :: rest) sendStaged = (do
        _ ← branch .setDevKeyPeerIter true
        keyPeerSource pid sendStaged
        keyPeerLoopSource rest sendStaged) := by
      simp [keyPeerLoopSource, List.forIn_cons, bind_assoc]
    have observedFactor : (do let _ ← observedKeyPeerLoopSource (pid :: rest) sendStaged; pure ()) = (do
        _ ← branch .setDevKeyPeerIter true
        let _ ← observedKeyPeerSource pid sendStaged
        let _ ← observedKeyPeerLoopSource rest sendStaged
        pure () : WG.M Unit) := by
      simp [observedKeyPeerLoopSource]
    rw [observedFactor, factor]
    have erased := observedKeyPeerSource_erase_device pid d sendStaged g marked device
    change (((observedKeyPeerSource pid sendStaged).run g).run marked >>= _) =
      (((keyPeerSource pid sendStaged).run g).run marked >>= _)
    change (((observedKeyPeerSource pid sendStaged).run g).run marked >>= _) = _ at erased
    cases headRun : ((observedKeyPeerSource pid sendStaged).run g).run marked with
    | error error =>
      rw [headRun] at erased
      rw [← erased]
      rfl
    | ok pair =>
      obtain ⟨⟨observation, current⟩, inputs⟩ := pair
      obtain ⟨p, _, effect⟩ := keyPeer_full_step pid d sendStaged
        g marked observation current inputs device headRun
      obtain ⟨next, nextDevice⟩ := keyPeerObservation_device d pid p sendStaged observation
        (Campaign2.snapshot current inputs) effect
      rw [headRun] at erased
      rw [← erased]
      exact ih next current inputs nextDevice

/-- The original identity/cookie prefix, including both short-circuited flags
and the peer-list snapshot read after the prefix. -/
def keyInstallObservationPrefix (key : Key) : WG.M (List PeerId × Bool) := do
  let d ← getDev
  let sendStaged ← WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
    (branch .setDevSendStagedRunning d.running)
  setStaticIdentityPrivateKey key
  let hasIdentity := (← getDev).staticIdentity.hasIdentity
  let sendStaged ← WG.andM (branch .setDevSendStagedKept sendStaged)
    (branch .setDevSendStagedHasIdentity hasIdentity)
  cookiePrecomputeDeviceKeys
  return ((← getDev).peerList, sendStaged)

private theorem keyInstallObservationPrefix_returns (d : Device) (key : Key) :
    Returns (keyInstallObservationPrefix key) (fun g => g.dev = some d)
      (fun selection g => selection = (d.peerList, requestsStagedSend d key) ∧
        g.dev = some (installedDevice d key)) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let first := mark ambient .setDevSendStagedNoIdentity (!d.staticIdentity.hasIdentity)
  let before := if !d.staticIdentity.hasIdentity then mark first .setDevSendStagedRunning d.running else first
  let requested := !d.staticIdentity.hasIdentity && d.running
  obtain ⟨u, identityState, identityAmbient, identityRun, identityDevice⟩ :=
    setStaticIdentity_returns key d g before device
  cases u
  let kept := mark identityAmbient .setDevSendStagedKept requested
  let middle := if requested then mark kept .setDevSendStagedHasIdentity
    (identityAfter key d.staticIdentity).hasIdentity else kept
  obtain ⟨u, cookieState, cookieAmbient, cookieRun, cookieDevice⟩ :=
    cookiePrecompute_returns {d with staticIdentity := identityAfter key d.staticIdentity}
      identityState middle identityDevice
  cases u
  refine ⟨(d.peerList, requestsStagedSend d key), cookieState, cookieAmbient, ?_, rfl, cookieDevice⟩
  cases old : d.staticIdentity.hasIdentity <;> cases running : d.running <;>
    cases new : (identityAfter key d.staticIdentity).hasIdentity
  all_goals simp [before, first, requested, middle, kept, mark, old, running, new] at identityRun cookieRun
  all_goals simp [keyInstallObservationPrefix, WG.andM, getDev, device, branch, AmbientM.branch, old, running]
  all_goals rw [identityRun]
  all_goals dsimp only [bind, Except.bind]
  all_goals simp [identityDevice, new, pure, StateT.pure, StateT.run, Except.pure]
  all_goals dsimp only [StateT.run] at cookieRun
  all_goals rw [cookieRun]
  all_goals dsimp only [bind, Except.bind]
  all_goals simp [cookieDevice, cookieKeysAfter, requestsStagedSend, old, running, new]
  all_goals rfl

def observedKeyInstallSource (key : Key) : WG.M (List (Option (Int64 × Option Bool))) := do
  let (pids, sendStaged) ← keyInstallObservationPrefix key
  let observations ← observedKeyPeerLoopSource pids sendStaged
  _ ← branch .setDevKeyPeerIter false
  return observations

theorem observedKeyInstallSource_erase (key : Key) (d : Device)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    (((do let _ ← observedKeyInstallSource key; pure ()) : WG.M Unit).run g).run ambient =
      ((keyInstallSource key).run g).run ambient := by
  have factor : keyInstallSource key = (do
      let (pids, sendStaged) ← keyInstallObservationPrefix key
      keyPeerLoopSource pids sendStaged
      _ ← branch .setDevKeyPeerIter false) := by
    simp [keyInstallSource, keyInstallObservationPrefix, bind_assoc]
  obtain ⟨selection, current, inputs, prefixRun, selectionEffect, currentDevice⟩ :=
    keyInstallObservationPrefix_returns d key g ambient device
  subst selection
  have observedFactor : (do let _ ← observedKeyInstallSource key; pure ()) = (do
      let (pids, sendStaged) ← keyInstallObservationPrefix key
      let _ ← observedKeyPeerLoopSource pids sendStaged
      _ ← branch .setDevKeyPeerIter false
      pure () : WG.M Unit) := by
    simp [observedKeyInstallSource]
  rw [observedFactor, factor]
  change (((keyInstallObservationPrefix key).run g).run ambient >>= _) =
    (((keyInstallObservationPrefix key).run g).run ambient >>= _)
  rw [prefixRun]
  have erased := observedKeyPeerLoopSource_erase d.peerList (installedDevice d key)
    (requestsStagedSend d key) current inputs currentDevice
  change (((observedKeyPeerLoopSource d.peerList (requestsStagedSend d key)).run current).run inputs >>= _) = _ at erased
  change (((observedKeyPeerLoopSource d.peerList (requestsStagedSend d key)).run current).run inputs >>= _) =
    (((keyPeerLoopSource d.peerList (requestsStagedSend d key)).run current).run inputs >>= _)
  rw [← erased]
  cases ((observedKeyPeerLoopSource d.peerList (requestsStagedSend d key)).run current).run inputs <;> rfl

theorem keyInstall_complete (d : Device) (key : Key) :
    Campaign2.Ensures (observedKeyInstallSource key) (fun s => s.wg.device = some d)
      (fun observations s => ∃ final, s.wg.device = some final ∧
        ObservedKeyPeerRun (requestsStagedSend d key) (installedDevice d key) d.peerList observations final) := by
  intro g ambient observations final after device run
  obtain ⟨selection, current, inputs, prefixRun, selectionEffect, currentDevice⟩ :=
    keyInstallObservationPrefix_returns d key g ambient device
  subst selection
  change (((keyInstallObservationPrefix key).run g).run ambient >>= _) = _ at run
  rw [prefixRun] at run
  change (((observedKeyPeerLoopSource d.peerList (requestsStagedSend d key)).run current).run inputs >>= _) = _ at run
  cases loopRun : ((observedKeyPeerLoopSource d.peerList (requestsStagedSend d key)).run current).run inputs with
  | error error => rw [loopRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨found, out⟩, ending⟩ := pair
    rw [loopRun] at run
    simp [branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact keyPeerLoop_complete d.peerList (installedDevice d key) (requestsStagedSend d key)
      current inputs found out ending currentDevice loopRun

end Leanux.Proofs.WG.Config
