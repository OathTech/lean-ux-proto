import Leanux.Proofs.WG.Config.Model
import Leanux.Proofs.WG.Config.Fwmark

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def sourcesClear (k : WGWorld) (pids : List PeerId) : Prop :=
  ∀ pid ∈ pids, ∃ p, (k.dev.bind fun d => d.peers[pid]?) = some p ∧ sourceClear p

theorem clearEndpointSource_missing (pid : PeerId) :
    Ensures (clearPeerEndpointSrc pid) (fun w => peerAt w pid = none)
      (fun _ _ => False) := by
  intro g ambient result final after absent run
  cases device : g.dev with
  | none =>
    simp [clearPeerEndpointSrc, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have missing : d.peers[pid]? = none := by simpa [peerAt, device] using absent
    simp [clearPeerEndpointSrc, getPeer, getDev, device, missing, invariant, AmbientM.invariant] at run
    cases run

theorem clearEndpointSource_accum (pid : PeerId) (seen : List PeerId) :
    Ensures (clearPeerEndpointSrc pid) (fun w => sourcesClear w seen)
      (fun _ w => sourcesClear w (seen ++ [pid])) := by
  intro w ambient ret v after hs hr
  cases hd : w.dev with
  | none =>
    exact False.elim (clearEndpointSource_missing pid w ambient ret v after (by simp [peerAt, hd]) hr)
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      exact False.elim (clearEndpointSource_missing pid w ambient ret v after (by simp [peerAt, hd, hp]) hr)
    | some p =>
      obtain ⟨d', reset, hv, _, hpid, hother⟩ :=
        clearEndpointSource_exact pid d p hp w ambient ret v after hd hr
      intro q hq
      by_cases heq : q = pid
      · subst q
        refine ⟨clearedSource p reset, by simp [hv, hpid], ?_⟩
        simp [sourceClear, clearedSource]
      · have hseen : q ∈ seen := by simpa [heq] using hq
        obtain ⟨old, hold, hclear⟩ := hs q hseen
        refine ⟨old, ?_, hclear⟩
        simpa [hv, hother q heq] using (show d.peers[q]? = some old by simpa [hd] using hold)

theorem clearEndpointSource_accum_frame (pid : PeerId) (seen : List PeerId)
    (initial : Option Device) :
    ⦃fun w => ⌜w.dev.map withoutPeers = initial ∧ sourcesClear w seen⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜w.dev.map withoutPeers = initial ∧ sourcesClear w (seen ++ [pid])⌝⦄ := by
  rw [← ensures_iff]
  intro w ambient ret v after h hr
  exact ⟨(ensures_iff _ _ _).mpr (clearEndpointSource_device_frame pid initial) w ambient ret v after h.1 hr,
    clearEndpointSource_accum pid seen w ambient ret v after h.2 hr⟩

def fwmarkClearLoop (pids : List PeerId) : WG.M Unit := do
  for pid in pids do
    _ ← branch .setDevFwmarkPeerIter true
    clearPeerEndpointSrc pid

theorem fwmarkClearLoop_accum (pids seen : List PeerId) (initial : Option Device) :
    Ensures (fwmarkClearLoop pids)
      (fun w => w.dev.map withoutPeers = initial ∧ sourcesClear w seen)
      (fun _ w => w.dev.map withoutPeers = initial ∧ sourcesClear w (seen ++ pids)) := by
  induction pids generalizing seen with
  | nil =>
    intro g ambient result final after pre run
    cases run
    simpa using pre
  | cons pid rest ih =>
    have factor : fwmarkClearLoop (pid :: rest) = (do
        _ ← branch .setDevFwmarkPeerIter true
        clearPeerEndpointSrc pid
        fwmarkClearLoop rest) := by
      simp [fwmarkClearLoop, List.forIn_cons, bind_assoc]
    rw [factor]
    refine ensures_bind (Q := fun _ g => g.dev.map withoutPeers = initial ∧ sourcesClear g seen) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.branch .setDevFwmarkPeerIter true) _)
    · intro _
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (clearEndpointSource_accum_frame pid seen initial)) ?_
      intro _ g ambient result final after pre run
      simpa only [List.append_assoc, List.singleton_append] using
        ih (seen ++ [pid]) g ambient result final after pre run

def deviceFwmarkUpdateSource (a : DeviceAttrs) (flags : UInt32) : WG.M Int := do
  let zero (ret : Int) : WG.M Int := do
    _ ← branch .setDevZeroKey a.privateKey.isSome
    return ret
  modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  if ← branch .setDevFwmark a.fwmark.isSome then
    modifyDev fun d => { d with fwmark := a.fwmark.getD 0 }
    fwmarkClearLoop (← getDev).peerList
    _ ← branch .setDevFwmarkPeerIter false
  if ← branch .setDevPort a.listenPort.isSome then
    let ret ← setPort (a.listenPort.getD 0)
    if ← branch .setDevPortErr (ret != 0) then return ← zero ret
  if ← branch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0) then peerRemoveAll
  deviceKeySource a

theorem deviceUpdate_loop_factor (a : DeviceAttrs) (flags : UInt32) :
    deviceFwmarkUpdateSource a flags = deviceUpdateSource a flags := by
  simp [deviceFwmarkUpdateSource, deviceUpdateSource, fwmarkClearLoop]

theorem fwmarkClearLoop_all (pids : List PeerId) (initial : Option Device) :
    ⦃fun w => ⌜w.dev.map withoutPeers = initial⌝⦄ fwmarkClearLoop pids
    ⦃⇓? _ w => ⌜w.dev.map withoutPeers = initial ∧ sourcesClear w pids⌝⦄ := by
  rw [← ensures_iff]
  intro w ambient ret v after hp hr
  simpa using fwmarkClearLoop_accum pids [] initial w ambient ret v after
    ⟨hp, by simp [sourcesClear]⟩ hr

theorem setDevice_fwmark_sources (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.dev.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        sourcesClear w d.peerList) := by
  let updated := {d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1}
  let Q : WGWorld → Prop := fun g => g.dev.map withoutPeers = some (withoutPeers updated) ∧ sourcesClear g d.peerList
  let tail : WG.M Int := do
    fwmarkClearLoop d.peerList
    _ ← branch .setDevFwmarkPeerIter false
    _ ← branch .setDevPort false
    _ ← branch .setDevReplacePeers false
    _ ← branch .setDevHasPrivateKey false
    _ ← branch .setDevHasPeers false
    _ ← branch .setDevZeroKey false
    pure 0
  have contract : Ensures tail
      (fun g => g.dev.map withoutPeers = some (withoutPeers updated))
      (fun ret g => ret = 0 ∧ Q g) := by
    unfold tail
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (fwmarkClearLoop_all d.peerList _)) ?_
    intro _ g ambient result final after pre run
    simp [branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, pre⟩
  intro g ambient result final after pre run
  obtain ⟨value, middle, next, lookupRun, lookupValue, device⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index d) g ambient pre
  subst value
  let logged (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := logged (logged (logged (logged (logged (logged (logged (logged (logged next
    .setDevLookupErr false) .setDevHasFlags false) .setDevBadFlags false)
    .setDevHasPort false) .setDevHasFwmark true) .setDevNoNet false)
    .setDevNotCapable false) .setDevPermErr false) .setDevFwmark true
  have source : ((wgSetDevice (fwmarkAttrs d mark)).run g).run ambient =
      (tail.run {middle with dev := some updated}).run before := by
    rw [← wgSetDevice_source]
    simp only [wgSetDeviceSource, ← deviceUpdate_loop_factor]
    simp [fwmarkAttrs, WG.orM, branch, AmbientM.branch,
      WGDEVICE_F_ALL]
    rw [show ((lookupInterface (byIndex d)).run g).run ambient =
      .ok ((.ok (), middle), next) from lookupRun]
    dsimp only [bind, Except.bind]
    simp [deviceFwmarkUpdateSource, deviceKeySource, devicePeersSource,
      WG.andM, branch, AmbientM.branch, getDev, device, net, modifyDev,
      WGDEVICE_F_REPLACE_PEERS, tail, fwmarkClearLoop, updated, before, logged,
      StateT.run, StateT.bind, StateT.lift, StateT.pure, Except.bind, Except.pure,
      liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
      MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get, Functor.map, StateT.map]
  exact contract _ before result final after (by simp) (source.symm.trans run)

end Leanux.Proofs.WG.Config
