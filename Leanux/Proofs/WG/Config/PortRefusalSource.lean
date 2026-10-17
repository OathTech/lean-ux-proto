import Leanux.Proofs.WG.Config.PortRefusalModel
import Leanux.Proofs.WG.Config.PortRefusalFrames
import Leanux.Proofs.WG.Config.DevicePorts
import Leanux.Proofs.WG.Config.ScalarGetterSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- Actual source order for a supported mixed request: a port-bind refusal comes
after both clearing loops, before replacement, identity, and peer attributes.
Missing peers and reset records remain possible Stops. -/
theorem setDevice_mixed_port_refused (d : Device) (mark port : Nat)
    (flags : Option UInt32) (key : Option Key) (peers : Option (List PeerEntry))
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices)
    (supported : flags.getD 0 &&& ~~~WGDEVICE_F_ALL = 0)
    (net : d.creatingNet = true) (running : d.running = true)
    (nonzero : port ≠ 0) (changed : d.incomingPort ≠ port)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true) :
    Ensures (wgSetDevice (portRefusalAttrs d mark port flags key peers))
      (fun g => g.dev = some d ∧ selectsDevice g d ∧ g.portBound = bound ∧
        readbackFrame g sock fixtures)
      (fun ret g => ret = -EADDRINUSE ∧ readbackFrame g sock fixtures ∧
        g.dev.map withoutPeers = some (withoutPeers (portRefusalBase d mark)) ∧
        clearedPeers d g d.peerList) := by
  let updated := portRefusalBase d mark
  let P : WGWorld → Prop := fun g =>
    g.dev.map withoutPeers = some (withoutPeers updated) ∧
    clearedPeers d g d.peerList ∧ g.portBound = bound ∧ readbackFrame g sock fixtures
  let Q : Int → WGWorld → Prop := fun ret g =>
    ret = -EADDRINUSE ∧ readbackFrame g sock fixtures ∧
    g.dev.map withoutPeers = some (withoutPeers updated) ∧ clearedPeers d g d.peerList
  let finish : Int → WG.M Int := fun ret => do
    if ← branch .setDevPortErr (ret != 0) then
      _ ← branch .setDevZeroKey key.isSome
      return ret
    if ← branch .setDevReplacePeers (flags.getD 0 &&& WGDEVICE_F_REPLACE_PEERS != 0) then peerRemoveAll
    deviceKeySource (portRefusalAttrs d mark port flags key peers)
  have finishRefused : Ensures (finish (-EADDRINUSE)) (fun g => Q (-EADDRINUSE) g) Q := by
    intro g ambient value final after pre run
    simp [finish, EADDRINUSE, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  have socket : Ensures (socketInit port) P Q := by
    intro g ambient value final after pre run
    obtain ⟨current, device, frame⟩ := Option.map_eq_some_iff.mp pre.1
    have sameNet : current.creatingNet = true := (congrArg Device.creatingNet frame).trans net
    have same4 : current.sock4 = d.sock4 := by simpa [withoutPeers, updated, portRefusalBase] using congrArg Device.sock4 frame
    have same6 : current.sock6 = d.sock6 := by simpa [withoutPeers, updated, portRefusalBase] using congrArg Device.sock6 frame
    have held : (bound port || current.sock4 == some port || current.sock6 == some port) = true := by
      simpa [same4, same6] using collision
    obtain ⟨code, _, preserved⟩ := socketInit_nonzero_collision_frame current port bound nonzero sameNet held P
      g ambient value final after ⟨device, pre.2.2.1, pre⟩ run
    exact ⟨code, preserved.2.2.2, preserved.1, preserved.2.1⟩
  have portContract : Ensures (setPort port) P Q := by
    let tail : WG.M Int := do
      _ ← branch .setPortPeerIter false
      if ← branch .setPortNotRunning false then
        modifyDev fun d => {d with incomingPort := port}
        return 0
      socketInit port
    have loop : Ensures (portClearLoop d.peerList) P (fun _ => P) := by
      intro g ambient value final after pre run
      obtain ⟨frame, cleared, held⟩ := portClearLoop_effects d d.peerList d.peerList
        (some (withoutPeers updated)) bound g ambient value final after
        ⟨pre.1, pre.2.1, pre.2.2.1⟩ run
      have saved := endpointClearLoop_configurationFrame .setPortPeerIter d.peerList bound sock fixtures
        g ambient value final after pre.2.2 run
      refine ⟨frame, ?_, held, saved.2⟩
      simpa [clearedPeers, List.mem_append] using cleared
    have whole : Ensures (do portClearLoop d.peerList; tail) P Q := by
      refine ensures_bind _ _ loop ?_
      intro _ g ambient value final after pre run
      exact socket g _ value final after pre (by simpa [tail, branch, AmbientM.branch] using run)
    intro g ambient value final after pre run
    obtain ⟨current, device, frame⟩ := Option.map_eq_some_iff.mp pre.1
    have samePort : current.incomingPort = d.incomingPort := by simpa [withoutPeers, updated, portRefusalBase] using congrArg Device.incomingPort frame
    have sameRun : current.running = true := (congrArg Device.running frame).trans running
    have samePeers : current.peerList = d.peerList := by simpa [withoutPeers, updated, portRefusalBase] using congrArg Device.peerList frame
    let start := {ambient with steps := ambient.steps.push {
      decision := .setPortSame, outcome := false, netRx := ambient.netRxSection}}
    have different : (d.incomingPort == port) = false := by simpa using changed
    have factor : ((setPort port).run g).run ambient =
        (((do portClearLoop d.peerList; tail) : WG.M Int).run g).run start := by
      rw [← setPort_source]
      simp [setPortSource, getDev, device, samePort, sameRun, samePeers, changed, different,
        branch, AmbientM.branch, tail, start]
    exact whole g start value final after pre (factor.symm.trans run)
  let afterClear : WG.M Int := do
    _ ← branch .setDevFwmarkPeerIter false
    _ ← branch .setDevPort true
    setPort port >>= finish
  have suffix : Ensures afterClear P Q := by
    have hbind : Ensures (setPort port >>= finish) P Q := by
      refine ensures_bind _ _ portContract ?_
      intro ret g ambient value final after pre run
      have code := pre.1
      subst ret
      exact finishRefused g ambient value final after pre run
    intro g ambient value final after pre run
    exact hbind g _ value final after pre (by simpa [afterClear, branch, AmbientM.branch] using run)
  have whole : Ensures (do fwmarkClearLoop d.peerList; afterClear)
      (fun g => g.dev = some updated ∧ g.portBound = bound ∧ readbackFrame g sock fixtures) Q := by
    refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => suffix)
    intro g ambient value final after pre run
    have effects := fwmarkClearLoop_effects d d.peerList [] (some (withoutPeers updated))
      g ambient value final after (by simp [clearedPeers, pre.1, updated, portRefusalBase]) run
    have saved := endpointClearLoop_configurationFrame .setDevFwmarkPeerIter d.peerList bound sock fixtures
      g ambient value final after pre.2 run
    exact ⟨effects.1, effects.2, saved⟩
  intro g ambient value final after pre run
  obtain ⟨looked, middle, next, lookupRun, result, device, held⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_bound d bound) g ambient
      ⟨pre.1, pre.2.1, pre.2.2.1⟩
  subst looked
  obtain ⟨looked, second, inputs, lookupAgain, result, _, saved⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_framed d sock fixtures) g ambient
      ⟨pre.1, pre.2.2.2, pre.2.1⟩
  rw [lookupRun] at lookupAgain
  cases lookupAgain
  let logged (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := logged (logged (logged (logged (logged (logged (logged (logged next
    .setDevLookupErr false) .setDevHasFlags flags.isSome) .setDevBadFlags false)
    .setDevHasPort true) .setDevNoNet false) .setDevNotCapable false)
    .setDevPermErr false) .setDevFwmark true
  have source : ((wgSetDevice (portRefusalAttrs d mark port flags key peers)).run g).run ambient =
      (((do fwmarkClearLoop d.peerList; afterClear) : WG.M Int).run {middle with dev := some updated}).run before := by
    rw [← wgSetDevice_source]
    simp only [wgSetDeviceSource, ← deviceUpdate_loop_factor]
    cases flags with
    | none =>
      simp [portRefusalAttrs, WG.orM, branch, AmbientM.branch,
        WGDEVICE_F_ALL]
      rw [lookupRun]
      dsimp only [bind, Except.bind]
      simp [deviceFwmarkUpdateSource, branch, AmbientM.branch, getDev, device, net, modifyDev,
        afterClear, finish, portRefusalAttrs, updated, portRefusalBase, before, logged,
        StateT.run, StateT.bind, StateT.lift, StateT.pure, Except.bind, Except.pure,
        liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
        MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get,
        Functor.map, StateT.map]
    | some flags =>
      simp only [Option.getD_some] at supported
      simp [portRefusalAttrs, WG.orM, branch, AmbientM.branch, supported]
      rw [lookupRun]
      dsimp only [bind, Except.bind]
      simp [deviceFwmarkUpdateSource, branch, AmbientM.branch, getDev, device, net, modifyDev,
        afterClear, finish, portRefusalAttrs, updated, portRefusalBase, before, logged,
        StateT.run, StateT.bind, StateT.lift, StateT.pure, Except.bind, Except.pure,
        liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
        MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get,
        Functor.map, StateT.map]
  exact whole {middle with dev := some updated} before value final after
    ⟨rfl, held, saved⟩ (source.symm.trans run)

end Leanux.Proofs.WG.Config
