import Leanux.Proofs.WG.Config.PortReadbackFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- The zero-port draw changes Ambient only. A collision remains an actual Stop;
normal socket creation preserves the bind lookup and getter readback fields. -/
theorem socketInit_zero_configurationFrame
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (socketInit 0)
      (fun g => g.portBound = bound ∧ readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.portBound = bound ∧ readbackFrame g sock fixtures
  have reinit (port : Nat) : Ensures (do socketReinit (some port) (some port); pure (0 : Int))
      P (fun _ => P) := by
    refine ensures_bind _ _ (socketReinit_configurationFrame _ _ bound sock fixtures) ?_
    intro _ g ambient value final after pre run
    cases run
    exact pre
  have tail (d : Device) (held : Nat → Bool) : Ensures (do
      let bs ← hidden .udpPortDraw
      let first := randomPortFirst (bs.foldr (fun b acc => acc * 256 + b.toNat) 0)
      if held first || d.sock4 == some first || d.sock6 == some first then
        unsupported "the random port draw collides with a bound port"
      socketReinit (some first) (some first)
      pure (0 : Int)) P (fun _ => P) := by
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden .udpPortDraw) P)
    · intro bs g ambient value final after pre run
      let first := randomPortFirst (bs.foldr (fun b acc => acc * 256 + b.toNat) 0)
      change (((do
        if held first || d.sock4 == some first || d.sock6 == some first then
          unsupported "the random port draw collides with a bound port"
        socketReinit (some first) (some first)
        pure (0 : Int)) : WG.M Int).run g).run ambient = _ at run
      by_cases collision : (held first || d.sock4 == some first || d.sock6 == some first) = true
      · simp [collision, unsupported, AmbientM.unsupported] at run
        cases run
      · exact reinit first g ambient value final after pre
          (by simpa only [show (held first || d.sock4 == some first || d.sock6 == some first) = false
            from Bool.eq_false_iff.mpr collision, Bool.false_eq_true, ite_false] using run)
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
      exact tail d g.portBound g ambient value final after pre
        (by simpa [socketInit, getDev, device, net] using run)

/-- Source clearing, down-state updates, and socket initialization leave the
configuration lookup and getter socket untouched, including same-port calls. -/
theorem setPort_zero_configurationFrame
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (setPort 0)
      (fun g => g.portBound = bound ∧ readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => g.portBound = bound ∧ readbackFrame g sock fixtures
  have tail (running : Bool) : Ensures (do
      _ ← branch .setPortPeerIter false
      if ← branch .setPortNotRunning !running then
        modifyDev fun d => {d with incomingPort := 0}
        return (0 : Int)
      socketInit 0) P (fun _ => P) := by
    intro g ambient value final after pre run
    cases running with
    | true =>
      exact socketInit_zero_configurationFrame bound sock fixtures
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
        modifyDev fun d => {d with incomingPort := 0}
        return (0 : Int)
      socketInit 0) P (fun _ => P) := by
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
    by_cases same : d.incomingPort = 0
    · simp [setPortSource, getDev, device, same, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    · exact whole d g _ value final after pre
        (by simpa [setPortSource, getDev, device, same, branch, AmbientM.branch] using run)

/-- Normal zero-port setter returns preserve the actual getter socket and
selector. This does not assert that the random draw or source clearing succeeds. -/
theorem setDevice_port_zero_configurationFrame (d : Device)
    (bound : Nat → Bool) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (wgSetDevice (portAttrs d 0))
      (fun g => g.dev = some d ∧ selectsDevice g d ∧ g.portBound = bound ∧
        readbackFrame g sock fixtures)
      (fun _ g => g.portBound = bound ∧ readbackFrame g sock fixtures) := by
  exact setDevice_port_configurationFrame_of_setPort d 0 bound sock fixtures
    (setPort_zero_configurationFrame bound sock fixtures)

end Leanux.Proofs.WG.Config
