import Leanux.Proofs.WG.Config.ClearedSources

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Pointwise store effects; map balancing is not an observable peer field. -/
def clearedPeers (initial : Device) (k : WGWorld) (seen : List PeerId) : Prop :=
  ∀ q, if q ∈ seen then
    ∃ p reset, initial.peers[q]? = some p ∧
      (k.dev.bind fun d => d.peers[q]?) = some (clearedSource p reset)
  else (k.dev.bind fun d => d.peers[q]?) = initial.peers[q]?

theorem clearedSource_twice (p : Peer) (first second : UInt64) :
    clearedSource (clearedSource p first) second = clearedSource p second := by
  simp [clearedSource, Option.map_map, Function.comp_def]

theorem clearEndpointSource_effects (initial : Device) (pid : PeerId) (seen : List PeerId) :
    Ensures (clearPeerEndpointSrc pid) (fun w => clearedPeers initial w seen)
      (fun _ w => clearedPeers initial w (seen ++ [pid])) := by
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
      intro q
      by_cases heq : q = pid
      · subst q
        simp only [List.mem_append, List.mem_singleton, or_true, ite_true]
        by_cases hseen : pid ∈ seen
        · obtain ⟨old, prior, hold, hprevious⟩ :=
            (show ∃ old prior, initial.peers[pid]? = some old ∧
              (w.dev.bind fun d => d.peers[pid]?) = some (clearedSource old prior) by
                simpa [hseen] using hs pid)
          have heqp : p = clearedSource old prior := by simpa [hd, hp] using hprevious
          refine ⟨old, reset, hold, ?_⟩
          simp [hv, hpid, heqp, clearedSource_twice]
        · have hold : some p = initial.peers[pid]? := by simpa [hseen, hd, hp] using hs pid
          exact ⟨p, reset, hold.symm, by simp [hv, hpid]⟩
      · have hlookup : (v.dev.bind fun d => d.peers[q]?) =
            (w.dev.bind fun d => d.peers[q]?) := by simp [hv, hd, hother q heq]
        simpa only [List.mem_append, List.mem_singleton, heq, or_false, hlookup] using hs q

theorem clearEndpointSource_effects_frame (initial : Device) (pid : PeerId)
    (seen : List PeerId) (frame : Option Device) :
    ⦃fun w => ⌜w.dev.map withoutPeers = frame ∧ clearedPeers initial w seen⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜w.dev.map withoutPeers = frame ∧ clearedPeers initial w (seen ++ [pid])⌝⦄ := by
  rw [← ensures_iff]
  intro w ambient ret v after h hr
  exact ⟨(ensures_iff _ _ _).mpr (clearEndpointSource_device_frame pid frame) w ambient ret v after h.1 hr,
    clearEndpointSource_effects initial pid seen w ambient ret v after h.2 hr⟩

theorem fwmarkClearLoop_effects (initial : Device) (pids seen : List PeerId) (frame : Option Device) :
    Ensures (fwmarkClearLoop pids)
      (fun w => w.dev.map withoutPeers = frame ∧ clearedPeers initial w seen)
      (fun _ w => w.dev.map withoutPeers = frame ∧ clearedPeers initial w (seen ++ pids)) := by
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
    refine ensures_bind (Q := fun _ g => g.dev.map withoutPeers = frame ∧ clearedPeers initial g seen) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.branch .setDevFwmarkPeerIter true) _)
    · intro _
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (clearEndpointSource_effects_frame initial pid seen frame)) ?_
      intro _ g ambient result final after pre run
      simpa only [List.append_assoc, List.singleton_append] using
        ih (seen ++ [pid]) g ambient result final after pre run

theorem setDevice_fwmark_effects (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.dev.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        clearedPeers d w d.peerList) := by
  let updated := {d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1}
  let Q : WGWorld → Prop := fun g => g.dev.map withoutPeers = some (withoutPeers updated) ∧ clearedPeers d g d.peerList
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
      (fun g => g.dev.map withoutPeers = some (withoutPeers updated) ∧ clearedPeers d g [])
      (fun ret g => ret = 0 ∧ Q g) := by
    unfold tail
    refine ensures_bind _ _ (fwmarkClearLoop_effects d d.peerList [] _) ?_
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
  exact contract _ before result final after (by simp [clearedPeers, updated]) (source.symm.trans run)

end Leanux.Proofs.WG.Config
