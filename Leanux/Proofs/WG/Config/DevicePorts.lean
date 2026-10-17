import Leanux.Proofs.WG.Config.RunningPort

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def portAttrs (d : Device) (port : Nat) : DeviceAttrs :=
  { device := byIndex d, listenPort := some port }

theorem lookupInterface_index_bound (d : Device) (bound : Nat → Bool) :
    ⦃fun w => ⌜w.dev = some d ∧ selectsDevice w d ∧ w.portBound = bound⌝⦄ lookupInterface (byIndex d)
    ⦃⇓ ret w => ⌜ret = .ok () ∧ w.dev = some d ∧ w.portBound = bound⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let after := mark (mark (mark (mark (mark (mark (mark ambient
    .lookupBothOrNeither false) .lookupHasIfindex true) .lookupNoDev false)
    .lookupNoLinkOps false) .lookupNoKind false) .lookupKindMismatch false) .lookupNotWireguard false
  refine ⟨.ok (), g, after, ?_, rfl, pre.1, pre.2.2⟩
  have selected := pre.2.1
  simp [selectsDevice] at selected
  simp [lookupInterface, byIndex, netDevices, pre.1, selected, WG.orM,
    branch, AmbientM.branch, after, mark]
  rfl

theorem setDevice_port_nonzero (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (net : d.creatingNet = true) (bound : Nat → Bool) :
    Ensures (wgSetDevice (portAttrs d port))
      (fun w => w.dev = some d ∧ selectsDevice w d ∧ w.portBound = bound)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        if d.incomingPort = port then ret = 0 ∧ w.dev = some updated
        else ret = (portOutcome updated port bound).1 ∧
          w.dev.map withoutPeers = some (withoutPeers (portOutcome updated port bound).2) ∧
          clearedPeers d w d.peerList) := by
  let updated := {d with deviceUpdateGen := d.deviceUpdateGen + 1}
  let effects : Int → WGWorld → Prop := fun ret g =>
    if d.incomingPort = port then ret = 0 ∧ g.dev = some updated
    else ret = (portOutcome updated port bound).1 ∧
      g.dev.map withoutPeers = some (withoutPeers (portOutcome updated port bound).2) ∧
      clearedPeers d g d.peerList
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
  have whole : Ensures (setPort port >>= finish)
      (fun g => g.dev = some updated ∧ g.portBound = bound) effects := by
    refine ensures_bind _ _ ?_ tail
    intro g ambient result final after pre run
    have post := setPort_nonzero_effects updated port nonzero bound g ambient result final after pre run
    simpa [effects, updated, clearedPeers] using post
  intro g ambient result final after pre run
  obtain ⟨value, middle, next, lookupRun, lookupValue, device, boundAt⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index_bound d bound) g ambient pre
  subst value
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
    ⟨rfl, boundAt⟩ (source.symm.trans run)

end Leanux.Proofs.WG.Config
