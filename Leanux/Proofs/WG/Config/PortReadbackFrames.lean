import Leanux.Proofs.WG.Config.PortRefusalFrames
import Leanux.Proofs.WG.Config.DevicePorts
import Leanux.Proofs.WG.Config.ScalarGetterSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- Actual socket replacement preserves the configuration lookup and readback state. -/
theorem socketReinit_configurationFrame (new4 new6 : Option Nat)
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (socketReinit new4 new6)
      (fun g => g.portBound = bound ∧ readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  intro g ambient value final after pre run
  cases device : g.dev with
  | none =>
    simp [socketReinit, getDev, device] at run
    change Except.error (Stop.invariant "no WireGuard device in this trace's fixture") =
      .ok ((value, final), after) at run
    contradiction
  | some d =>
    cases new4 <;> cases old4 : d.sock4 <;> cases old6 : d.sock6
    all_goals simp [socketReinit, getDev, device, modifyDev, branch, AmbientM.branch,
      sockFree, iputReport, AmbientM.iputReport, old4, old6] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact pre

/-- Nonzero socket initialization preserves readback state on every normal branch. -/
theorem socketInit_nonzero_configurationFrame (port : Nat) (nonzero : port ≠ 0)
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (socketInit port)
      (fun g => g.portBound = bound ∧ readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.portBound = bound ∧ readbackFrame g sock fixtures
  have tail : Ensures (do socketReinit (some port) (some port); pure (0 : Int)) P
      (fun _ => P) := by
    refine ensures_bind _ _ (socketReinit_configurationFrame _ _ bound sock fixtures) ?_
    intro _ g ambient value final after pre run
    cases run
    exact pre
  intro g ambient value final after pre run
  cases device : g.dev with
  | none =>
    simp [socketInit, getDev, device] at run
    change Except.error (Stop.invariant "no WireGuard device in this trace's fixture") =
      .ok ((value, final), after) at run
    contradiction
  | some d =>
    cases net : d.creatingNet with
    | false =>
      simp [socketInit, getDev, device, net] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    | true =>
      by_cases collision : (g.portBound port || d.sock4 == some port || d.sock6 == some port) = true
      · simp only [Bool.or_eq_true, beq_iff_eq] at collision
        simp [socketInit, getDev, device, net, nonzero, collision,
          iputReport, AmbientM.iputReport, AmbientM.branch] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
      · simp only [Bool.or_eq_true, beq_iff_eq] at collision
        apply tail g ambient value final after pre
        simpa [socketInit, getDev, device, net, nonzero, collision] using run

/-- Source clearing, down-state updates, and socket initialization leave the
configuration lookup and getter socket untouched, including same-port calls. -/
theorem setPort_nonzero_configurationFrame (port : Nat) (nonzero : port ≠ 0)
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (setPort port)
      (fun g => g.portBound = bound ∧ readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.portBound = bound ∧ readbackFrame g sock fixtures
  have tail (running : Bool) : Ensures (do
      _ ← branch .setPortPeerIter false
      if ← branch .setPortNotRunning !running then
        modifyDev fun d => {d with incomingPort := port}
        return (0 : Int)
      socketInit port) P (fun _ => P) := by
    intro g ambient value final after pre run
    cases running with
    | true =>
      exact socketInit_nonzero_configurationFrame port nonzero bound sock fixtures
        g _ value final after pre (by simpa [branch, AmbientM.branch] using run)
    | false =>
      cases device : g.dev with
      | none =>
        simp [branch, AmbientM.branch, modifyDev, device] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
      | some d =>
        simp [branch, AmbientM.branch, modifyDev, device] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
  have whole (d : Device) : Ensures (do
      portClearLoop d.peerList
      _ ← branch .setPortPeerIter false
      if ← branch .setPortNotRunning !d.running then
        modifyDev fun d => {d with incomingPort := port}
        return (0 : Int)
      socketInit port) P (fun _ => P) := by
    exact ensures_bind _ _
      (endpointClearLoop_configurationFrame .setPortPeerIter d.peerList bound sock fixtures)
      (fun _ => tail d.running)
  intro g ambient value final after pre run
  rw [← setPort_source] at run
  cases device : g.dev with
  | none =>
    simp [setPortSource, getDev, device] at run
    change Except.error (Stop.invariant "no WireGuard device in this trace's fixture") =
      .ok ((value, final), after) at run
    contradiction
  | some d =>
    by_cases same : d.incomingPort = port
    · simp [setPortSource, getDev, device, same, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    · exact whole d g _ value final after pre
        (by simpa [setPortSource, getDev, device, same, branch, AmbientM.branch] using run)

/-- The original selected-device port request preserves the getter socket,
fixture selector, and bind lookup. No running, network, or clearing-success
premise is required; Stops remain outside this partial postcondition. -/
theorem setDevice_port_nonzero_configurationFrame (d : Device) (port : Nat)
    (nonzero : port ≠ 0) (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (wgSetDevice (portAttrs d port))
      (fun g => g.dev = some d ∧ selectsDevice g d ∧ g.portBound = bound ∧
        readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.portBound = bound ∧ readbackFrame g sock fixtures
  let updated := {d with deviceUpdateGen := d.deviceUpdateGen + 1}
  let finish : Int → WG.M Int := fun ret => do
    if ← branch .setDevPortErr (ret != 0) then
      _ ← branch .setDevZeroKey false
      return ret
    _ ← branch .setDevReplacePeers false
    _ ← branch .setDevHasPrivateKey false
    _ ← branch .setDevHasPeers false
    _ ← branch .setDevZeroKey false
    pure 0
  have tail (ret : Int) : Ensures (finish ret) P (fun _ => P) := by
    intro g ambient value final after pre run
    by_cases zero : ret = 0
    · subst ret
      simp [finish, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    · simp [finish, branch, AmbientM.branch, zero] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have whole : Ensures (setPort port >>= finish) P (fun _ => P) :=
    ensures_bind _ _ (setPort_nonzero_configurationFrame port nonzero bound sock fixtures) tail
  intro g ambient value final after pre run
  obtain ⟨looked, middle, next, lookupRun, result, device, boundAt⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_bound d bound) g ambient
      ⟨pre.1, pre.2.1, pre.2.2.1⟩
  subst looked
  obtain ⟨looked, second, inputs, lookupAgain, result, _, saved⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_framed d sock fixtures) g ambient
      ⟨pre.1, pre.2.2.2, pre.2.1⟩
  rw [lookupRun] at lookupAgain
  cases lookupAgain
  cases net : d.creatingNet with
  | false =>
    rw [← wgSetDevice_source] at run
    simp [wgSetDeviceSource, portAttrs, WG.orM, branch, AmbientM.branch, WGDEVICE_F_ALL] at run
    rw [lookupRun] at run
    dsimp only [bind, Except.bind] at run
    simp [getDev, device, net,
      StateT.run, StateT.bind, StateT.lift, StateT.pure, Except.bind, Except.pure,
      liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
      MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get,
      Functor.map, StateT.map] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨boundAt, saved⟩
  | true =>
    let logged (a : Ambient) (site : Decision) (value : Bool) :=
      {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
    let before := logged (logged (logged (logged (logged (logged (logged (logged (logged next
      .setDevLookupErr false) .setDevHasFlags false) .setDevBadFlags false)
      .setDevHasPort true) .setDevNoNet false) .setDevNotCapable false)
      .setDevPermErr false) .setDevFwmark false) .setDevPort true
    have source : ((wgSetDevice (portAttrs d port)).run g).run ambient =
        ((setPort port >>= finish).run {middle with dev := some updated}).run before := by
      rw [← wgSetDevice_source]
      simp [wgSetDeviceSource, portAttrs, WG.orM, branch, AmbientM.branch, WGDEVICE_F_ALL]
      rw [lookupRun]
      dsimp only [bind, Except.bind]
      simp [deviceUpdateSource, deviceKeySource, devicePeersSource,
        WG.andM, branch, AmbientM.branch, getDev, device, net, modifyDev,
        WGDEVICE_F_REPLACE_PEERS, finish, updated, before, logged,
        StateT.run, StateT.bind, StateT.lift, StateT.pure, Except.bind, Except.pure,
        liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
        MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get,
        Functor.map, StateT.map]
      split <;> rfl
    exact whole {middle with dev := some updated} before value final after
      ⟨boundAt, saved⟩ (source.symm.trans run)

end Leanux.Proofs.WG.Config
