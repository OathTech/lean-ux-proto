import Leanux.Proofs.WG.Config.Fwmark

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def sourceClear (p : Peer) : Prop :=
  (∀ e, p.endpoint = some e → e.src = 0 ∧ e.srcIf = 0) ∧ p.dstCache.slot = none

def sourcesClear (k : Kernel) (pids : List PeerId) : Prop :=
  ∀ pid ∈ pids, ∃ p, (k.wg.bind fun d => d.peers[pid]?) = some p ∧ sourceClear p

theorem clearEndpointSource_missing (pid : PeerId) :
    Ensures (clearPeerEndpointSrc pid) (fun w => peerAt w pid = none)
      (fun _ _ => False) := by
  rw [ensures_iff]
  have ht := unconstrained_prefix (dstCacheResetNow pid)
  mvcgen [clearPeerEndpointSrc, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, invariant, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt]

theorem clearEndpointSource_accum (pid : PeerId) (seen : List PeerId) :
    Ensures (clearPeerEndpointSrc pid) (fun w => sourcesClear w.k seen)
      (fun _ w => sourcesClear w.k (seen ++ [pid])) := by
  intro w ret v hs hr
  cases hd : w.k.wg with
  | none =>
    exact False.elim (clearEndpointSource_missing pid w ret v (by simp [peerAt, hd]) hr)
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      exact False.elim (clearEndpointSource_missing pid w ret v (by simp [peerAt, hd, hp]) hr)
    | some p =>
      obtain ⟨d', reset, hv, _, hpid, hother⟩ :=
        clearEndpointSource_exact pid d p hp w ret v hd hr
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
    ⦃fun w => ⌜w.k.wg.map withoutPeers = initial ∧ sourcesClear w.k seen⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜w.k.wg.map withoutPeers = initial ∧ sourcesClear w.k (seen ++ [pid])⌝⦄ := by
  rw [← ensures_iff]
  intro w ret v h hr
  exact ⟨(ensures_iff _ _ _).mpr (clearEndpointSource_device_frame pid initial) w ret v h.1 hr,
    clearEndpointSource_accum pid seen w ret v h.2 hr⟩

def fwmarkClearLoop (pids : List PeerId) : M Unit := do
  for pid in pids do
    _ ← branch .setDevFwmarkPeerIter true
    clearPeerEndpointSrc pid

theorem fwmarkClearLoop_accum (pids seen : List PeerId) (initial : Option Device) :
    Ensures (fwmarkClearLoop pids)
      (fun w => w.k.wg.map withoutPeers = initial ∧ sourcesClear w.k seen)
      (fun _ w => w.k.wg.map withoutPeers = initial ∧ sourcesClear w.k (seen ++ pids)) := by
  induction pids generalizing seen with
  | nil =>
    rw [ensures_iff]
    simp [fwmarkClearLoop]
    mvcgen
  | cons pid rest ih =>
    have factor : fwmarkClearLoop (pid :: rest) = (do
        _ ← branch .setDevFwmarkPeerIter true
        clearPeerEndpointSrc pid
        fwmarkClearLoop rest) := by
      simp [fwmarkClearLoop, List.forIn_cons, bind_assoc]
    have hc := clearEndpointSource_accum_frame pid seen initial
    have ht := (ensures_iff _ _ _).mp (ih (seen ++ [pid]))
    rw [factor, ensures_iff]
    mvcgen [branch, hc, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [List.append_assoc]

def deviceFwmarkUpdateSource (a : DeviceAttrs) (flags : UInt32) : M Int := do
  let zero (ret : Int) : M Int := do
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
  simp [deviceFwmarkUpdateSource, deviceUpdateSource, fwmarkClearLoop, bind_assoc]

theorem fwmarkClearLoop_all (pids : List PeerId) (initial : Option Device) :
    ⦃fun w => ⌜w.k.wg.map withoutPeers = initial⌝⦄ fwmarkClearLoop pids
    ⦃⇓? _ w => ⌜w.k.wg.map withoutPeers = initial ∧ sourcesClear w.k pids⌝⦄ := by
  rw [← ensures_iff]
  intro w ret v hp hr
  simpa using fwmarkClearLoop_accum pids [] initial w ret v
    ⟨hp, by simp [sourcesClear]⟩ hr

theorem setDevice_fwmark_sources (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        sourcesClear w.k d.peerList) := by
  let updated := withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index d
  have hc := fun pids => fwmarkClearLoop_all pids (some updated)
  rw [← wgSetDevice_source, ensures_iff]
  simp only [wgSetDeviceSource, ← deviceUpdate_loop_factor]
  simp [deviceFwmarkUpdateSource, deviceKeySource, devicePeersSource,
    fwmarkAttrs, branch, bind_assoc, Leanux.WG.andM, Leanux.WG.orM,
    WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [getDev, getK, modifyDev, modifyK, invariant, hl, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withoutPeers, updated]
  all_goals grind only

end Leanux.Proofs.WG.Config
