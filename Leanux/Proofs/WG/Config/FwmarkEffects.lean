import Leanux.Proofs.WG.Config.ClearedSources

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Pointwise store effects; map balancing is not an observable peer field. -/
def clearedPeers (initial : Device) (k : Kernel) (seen : List PeerId) : Prop :=
  ∀ q, if q ∈ seen then
    ∃ p reset, initial.peers[q]? = some p ∧
      (k.wg.bind fun d => d.peers[q]?) = some (clearedSource p reset)
  else (k.wg.bind fun d => d.peers[q]?) = initial.peers[q]?

theorem clearedSource_twice (p : Peer) (first second : UInt64) :
    clearedSource (clearedSource p first) second = clearedSource p second := by
  simp [clearedSource, Option.map_map, Function.comp_def]

theorem clearEndpointSource_effects (initial : Device) (pid : PeerId) (seen : List PeerId) :
    Ensures (clearPeerEndpointSrc pid) (fun w => clearedPeers initial w.k seen)
      (fun _ w => clearedPeers initial w.k (seen ++ [pid])) := by
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
      intro q
      by_cases heq : q = pid
      · subst q
        simp only [List.mem_append, List.mem_singleton, or_true, if_true]
        by_cases hseen : pid ∈ seen
        · obtain ⟨old, prior, hold, hprevious⟩ :=
            (show ∃ old prior, initial.peers[pid]? = some old ∧
              (w.k.wg.bind fun d => d.peers[pid]?) = some (clearedSource old prior) by
                simpa [hseen] using hs pid)
          have heqp : p = clearedSource old prior := by simpa [hd, hp] using hprevious
          refine ⟨old, reset, hold, ?_⟩
          simp [hv, hpid, heqp, clearedSource_twice]
        · have hold : some p = initial.peers[pid]? := by simpa [hseen, hd, hp] using hs pid
          exact ⟨p, reset, hold.symm, by simp [hv, hpid]⟩
      · have hlookup : (v.k.wg.bind fun d => d.peers[q]?) =
            (w.k.wg.bind fun d => d.peers[q]?) := by simp [hv, hd, hother q heq]
        simpa only [List.mem_append, List.mem_singleton, heq, or_false, hlookup] using hs q

theorem clearEndpointSource_effects_frame (initial : Device) (pid : PeerId)
    (seen : List PeerId) (frame : Option Device) :
    ⦃fun w => ⌜w.k.wg.map withoutPeers = frame ∧ clearedPeers initial w.k seen⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜w.k.wg.map withoutPeers = frame ∧ clearedPeers initial w.k (seen ++ [pid])⌝⦄ := by
  rw [← ensures_iff]
  intro w ret v h hr
  exact ⟨(ensures_iff _ _ _).mpr (clearEndpointSource_device_frame pid frame) w ret v h.1 hr,
    clearEndpointSource_effects initial pid seen w ret v h.2 hr⟩

theorem fwmarkClearLoop_effects (initial : Device) (pids seen : List PeerId) (frame : Option Device) :
    Ensures (fwmarkClearLoop pids)
      (fun w => w.k.wg.map withoutPeers = frame ∧ clearedPeers initial w.k seen)
      (fun _ w => w.k.wg.map withoutPeers = frame ∧ clearedPeers initial w.k (seen ++ pids)) := by
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
    have hc := clearEndpointSource_effects_frame initial pid seen frame
    have ht := (ensures_iff _ _ _).mp (ih (seen ++ [pid]))
    rw [factor, ensures_iff]
    mvcgen [branch, hc, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [List.append_assoc]

theorem setDevice_fwmark_effects (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        clearedPeers d w.k d.peerList) := by
  let updated := withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index d
  have hc := fun pids => (ensures_iff _ _ _).mp (fwmarkClearLoop_effects d pids [] (some updated))
  rw [← wgSetDevice_source, ensures_iff]
  simp only [wgSetDeviceSource, ← deviceUpdate_loop_factor]
  simp [deviceFwmarkUpdateSource, deviceKeySource, devicePeersSource,
    fwmarkAttrs, branch, bind_assoc, Leanux.WG.andM, Leanux.WG.orM,
    WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  mvcgen [getDev, getK, modifyDev, modifyK, invariant, hl, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withoutPeers, updated, clearedPeers]
  all_goals grind only

end Leanux.Proofs.WG.Config
