import Leanux.Proofs.WG.Config.ZeroPortDrawFrames
import Leanux.Proofs.WG.Config.DevicePorts

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem socketInit_zero_projected (d initial : Device) (seen : List PeerId)
    (net : d.creatingNet = true) :
    ⦃fun w => ⌜w.dev.map withoutPeers = some (withoutPeers d) ∧ clearedPeers initial w seen⌝⦄ socketInit 0
    ⦃⇓? ret w => ⌜ret = 0 ∧ clearedPeers initial w seen ∧ ∃ port,
      LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧
      w.dev.map withoutPeers = some (withoutPeers
        { d with sock4 := some port, sock6 := some port, incomingPort := port })⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨current, device, frame⟩ := Option.map_eq_some_iff.mp pre.1
  have currentNet : current.creatingNet = true := (congrArg Device.creatingNet frame).trans net
  obtain ⟨value, port, low, high, changed⟩ := socketInit_zero current currentNet
    g ambient result final after device run
  have changedFrame : withoutPeers {current with sock4 := some port, sock6 := some port, incomingPort := port} =
      withoutPeers {d with sock4 := some port, sock6 := some port, incomingPort := port} :=
    congrArg (fun state : Device => {state with sock4 := some port, sock6 := some port, incomingPort := port}) frame
  refine ⟨value, ?_, port, low, high, ?_⟩
  · simpa [clearedPeers, changed, device] using pre.2
  · simpa [changed] using congrArg some changedFrame

def zeroPortEffects (d : Device) (w : WGWorld) : Prop :=
  if d.incomingPort = 0 then w.dev = some d
  else clearedPeers d w d.peerList ∧
    if d.running then ∃ port,
      LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧
      w.dev.map withoutPeers = some (withoutPeers
        { d with sock4 := some port, sock6 := some port, incomingPort := port })
    else w.dev.map withoutPeers = some (withoutPeers { d with incomingPort := 0 })

theorem setPort_zero_bound (d : Device) (net : d.creatingNet = true) (bound : Nat → Bool) :
    Ensures (setPort 0) (fun w => w.dev = some d ∧ w.portBound = bound)
      (fun ret w => ret = 0 ∧ zeroPortEffects d w) := by
  let Q : WGWorld → Prop := fun g => g.dev.map withoutPeers = some (withoutPeers d) ∧
    clearedPeers d g d.peerList ∧ g.portBound = bound
  let R : Int → WGWorld → Prop := fun ret g => ret = 0 ∧ clearedPeers d g d.peerList ∧
    if d.running then ∃ port,
      LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧
      g.dev.map withoutPeers = some (withoutPeers
        {d with sock4 := some port, sock6 := some port, incomingPort := port})
    else g.dev.map withoutPeers = some (withoutPeers {d with incomingPort := 0})
  let tail : WG.M Int := do
    _ ← branch .setPortPeerIter false
    if ← branch .setPortNotRunning !d.running then
      modifyDev fun d => {d with incomingPort := 0}
      return 0
    socketInit 0
  have ht : Ensures tail Q R := by
    unfold tail
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .setPortPeerIter false) _)
    · intro _
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (branch_state_spec Q .setPortNotRunning (!d.running))) ?_
      intro decision g ambient result final after pre run
      obtain ⟨rfl, pre⟩ := pre
      cases running : d.running with
      | false =>
        simp only [running, Bool.not_false, ite_true] at run
        simp [modifyDev] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        obtain ⟨current, device, frame⟩ := Option.map_eq_some_iff.mp pre.1
        have changedFrame : withoutPeers {current with incomingPort := 0} = withoutPeers {d with incomingPort := 0} :=
          congrArg (fun state : Device => {state with incomingPort := 0}) frame
        refine ⟨rfl, ?_, ?_⟩
        · simpa [clearedPeers, device] using pre.2.1
        · simpa [running, device] using congrArg some changedFrame
      | true =>
        have post := (ensures_iff _ _ _).mpr (socketInit_zero_projected d d d.peerList net)
          g ambient result final after ⟨pre.1, pre.2.1⟩
          (by simpa only [running, Bool.not_true, Bool.false_eq_true, ite_false] using run)
        simpa [R, running] using post
  intro g ambient result final after pre run
  by_cases same : d.incomingPort = 0
  · simp [setPort, getDev, pre.1, branch, AmbientM.branch, same] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    simp [zeroPortEffects, same, pre.1]
  · have different : (d.incomingPort == 0) = false := by simp [same]
    let before := {ambient with steps := ambient.steps.push {
      decision := .setPortSame, outcome := false, netRx := ambient.netRxSection}}
    have source : ((setPort 0).run g).run ambient =
        (((do portClearLoop d.peerList; tail) : WG.M Int).run g).run before := by
      rw [← setPort_source]
      simp [setPortSource, getDev, pre.1, branch, AmbientM.branch, same, different, tail, before]
    have whole : Ensures (do portClearLoop d.peerList; tail)
        (fun g => g.dev.map withoutPeers = some (withoutPeers d) ∧ clearedPeers d g [] ∧ g.portBound = bound) R := by
      refine ensures_bind _ _ (portClearLoop_effects d d.peerList [] _ bound) ?_
      intro _
      exact ht
    have post := whole g before result final after (by simp [clearedPeers, pre.1, pre.2]) (source.symm.trans run)
    simpa [same, R, zeroPortEffects] using post

theorem setPort_zero_effects (d : Device) (net : d.creatingNet = true) :
    Ensures (setPort 0) (fun w => w.dev = some d)
      (fun ret w => ret = 0 ∧ zeroPortEffects d w) := by
  intro g ambient ret final after pre run
  exact setPort_zero_bound d net g.portBound g ambient ret final after ⟨pre, rfl⟩ run

theorem setDevice_port_zero (d : Device) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (portAttrs d 0))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ zeroPortEffects
        { d with deviceUpdateGen := d.deviceUpdateGen + 1 } w) := by
  let updated := {d with deviceUpdateGen := d.deviceUpdateGen + 1}
  let effects : Int → WGWorld → Prop := fun ret g => ret = 0 ∧ zeroPortEffects updated g
  let finish : Int → WG.M Int := fun ret => do
    if ← branch .setDevPortErr (ret != 0) then
      _ ← branch .setDevZeroKey false
      return ret
    _ ← branch .setDevReplacePeers false
    _ ← branch .setDevHasPrivateKey false
    _ ← branch .setDevHasPeers false
    _ ← branch .setDevZeroKey false
    pure 0
  have tail (ret : Int) : Ensures (finish ret) (effects ret) effects := by
    intro g ambient result final after pre run
    by_cases zero : ret = 0
    · subst ret
      simp [finish, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    · have different : (ret != 0) = true := by simp [zero]
      simp [finish, branch, AmbientM.branch, different, zero] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have whole : Ensures (setPort 0 >>= finish)
      (fun g => g.dev = some updated) effects := by
    exact ensures_bind _ _ (setPort_zero_effects updated net) tail
  intro g ambient result final after pre run
  obtain ⟨value, middle, next, lookupRun, lookupValue, device, _boundAt⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_bound d g.portBound) g ambient ⟨pre.1, pre.2, rfl⟩
  subst value
  let logged (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := logged (logged (logged (logged (logged (logged (logged (logged (logged next
    .setDevLookupErr false) .setDevHasFlags false) .setDevBadFlags false)
    .setDevHasPort true) .setDevNoNet false) .setDevNotCapable false)
    .setDevPermErr false) .setDevFwmark false) .setDevPort true
  have source : ((wgSetDevice (portAttrs d 0)).run g).run ambient =
      ((setPort 0 >>= finish).run {middle with dev := some updated}).run before := by
    rw [← wgSetDevice_source]
    simp [wgSetDeviceSource, portAttrs, WG.orM, branch, AmbientM.branch, WGDEVICE_F_ALL]
    rw [show ((lookupInterface (byIndex d)).run g).run ambient =
      .ok ((.ok (), middle), next) from lookupRun]
    dsimp only [bind, Except.bind]
    simp [deviceUpdateSource, deviceKeySource, devicePeersSource,
      WG.andM, branch, AmbientM.branch, getDev, device, net, modifyDev,
      WGDEVICE_F_REPLACE_PEERS, finish, updated, before, logged,
      StateT.run, StateT.bind, StateT.lift, StateT.pure, Except.bind, Except.pure,
      liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
      MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get, Functor.map, StateT.map]
    split <;> rfl
  exact whole {middle with dev := some updated} before result final after
    rfl (source.symm.trans run)

end Leanux.Proofs.WG.Config
