import Leanux.Proofs.WG.TimerDiscipline.RetryBaseSource
import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims
import Leanux.Proofs.WG.Config.EndpointSources
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem queuedDevice_retryView (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p) :
    ((queuedDevice d pid p now).peers[pid]?).map retryView =
      some (retryView p) := by
  unfold queuedDevice
  split
  · simp [resident]
  · split <;> simp [withPeer, retryView]

theorem sendQueuedRetry_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun g => ⌜retryAt g pid = some n⌝⦄ sendQueuedHandshakeInitiation pid true
      ⦃⇓? _ g => ⌜retryAt g pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      have hn : retryView p = n := by simpa [retryAt, peerAt, hd, hp] using pre
      rw [← observedSendQueuedRetry_erase] at run
      change ((((observedSendQueuedRetry pid).run g).run ambient) >>= fun ((_, current), inputs) =>
        .ok (((), current), inputs)) = _ at run
      cases observed : ((observedSendQueuedRetry pid).run g).run ambient with
      | error stop => rw [observed] at run; cases run
      | ok pair =>
        obtain ⟨⟨seen, current⟩, inputs⟩ := pair
        rw [observed] at run
        cases run
        have facts := sendQueuedRetry_exact pid d p hp g ambient seen final after hd observed
        cases inspected : seen.2 with
        | none =>
          simp only [inspected] at facts
          have device : final.dev = some d := facts.1
          simpa [retryAt, peerAt, device, hp] using congrArg some hn
        | some queued =>
          simp only [inspected] at facts
          have same : ((queuedDeviceAfterInspection d pid p seen.1 queued).peers[pid]?).map retryView = some (retryView p) := by
            unfold queuedDeviceAfterInspection
            split
            · simp [hp]
            · split <;> simp [withPeer, retryView]
          have device : final.dev = some (queuedDeviceAfterInspection d pid p seen.1 queued) := facts.2.2
          simpa [retryAt, peerAt, device, hn] using same

theorem clearEndpoint_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun g => ⌜retryAt g pid = some n⌝⦄ clearPeerEndpointSrc pid
      ⦃⇓? _ g => ⌜retryAt g pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      have hn : retryView p = n := by simpa [retryAt, peerAt, hd, hp] using pre
      obtain ⟨out, reset, device, _, peer, _⟩ :=
        clearEndpointSource_exact pid d p hp g ambient result final after hd run
      simpa [retryAt, peerAt, device, peer, clearedSource, retryView] using congrArg some hn

theorem modZero_retryView (site : HiddenSite) (pid : PeerId) (delay : Nat) (n : RetryView) :
    ⦃fun g => ⌜retryAt g pid = some n⌝⦄ modPeerTimer site pid .zeroKeyMaterial delay
      ⦃⇓? _ g => ⌜retryAt g pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      have hn : retryView p = n := by simpa [retryAt, peerAt, hd, hp] using pre
      obtain ⟨_, effect⟩ := modPeerTimer_effect site pid .zeroKeyMaterial delay d p hp
        (Campaign2.snapshot g ambient) g ambient result final after ⟨rfl, hd⟩ run
      change (((Campaign2.snapshot final after).wg.device.bind fun d => d.peers[pid]?).map retryView) = some n
      cases result with
      | false =>
        simp only [Bool.false_eq_true, ite_false] at effect
        refine (congrArg (fun state : Campaign2.State =>
          (state.device.bind fun dev => dev.peers[pid]?).map retryView) effect).trans ?_
        simpa [Campaign2.snapshot, Campaign2.core, hd, hp] using congrArg some hn
      | true =>
        simp only [ite_true] at effect
        cases mode : ambient.armRecords with
        | false =>
          simp only [peerTimerArmEffect, Campaign2.snapshot, mode, Bool.false_eq_true, ite_false] at effect
          refine (congrArg (fun state : Campaign2.State =>
            (state.device.bind fun dev => dev.peers[pid]?).map retryView) effect).trans ?_
          cases placed : TimerWheel.place p .zeroKeyMaterial
            (g.jiffiesLast.getD 0 + delay.toUInt64) (g.jiffiesLast.getD 0) <;>
            simp only [wheelPlacementView, placed]
          all_goals simp [Campaign2.core, hd, retryView, Peer.setTimer, Peer.setWheel, ← hn]
        | true =>
          simp only [peerTimerArmEffect, Campaign2.snapshot, mode, ite_true] at effect
          obtain ⟨caller, now, unit, _, _, effect⟩ := effect
          split at effect
          · refine (congrArg (fun state : Campaign2.State =>
              (state.device.bind fun dev => dev.peers[pid]?).map retryView) effect).trans ?_
            simpa [recordedArmPrefixView, Campaign2.core, hd, hp] using congrArg some hn
          · obtain ⟨clk, effect⟩ := effect
            refine (congrArg (fun state : Campaign2.State =>
              (state.device.bind fun dev => dev.peers[pid]?).map retryView) effect).trans ?_
            cases placed : TimerWheel.place p .zeroKeyMaterial (caller + delay.toUInt64) clk <;>
              simp only [wheelPlacementView, placed]
            all_goals simp [recordedArmPrefixView, Campaign2.core, hd,
              retryView, Peer.setTimer, Peer.setWheel, ← hn]

theorem delKeepalive_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun g => ⌜retryAt g pid = some n⌝⦄ delTimer pid .sendKeepalive
      ⦃⇓? _ g => ⌜retryAt g pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      simp [delTimer, getPeer, getDev, hd, hp, setPeer, modifyDev] at run
      rcases run with ⟨rfl, rfl⟩
      simpa [retryAt, peerAt, hd, hp, retryView, Peer.setTimer, Peer.setWheel] using pre

theorem purge_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun g => ⌜retryAt g pid = some n⌝⦄ purgeStagedPackets pid
      ⦃⇓? _ g => ⌜retryAt g pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases hd : g.dev with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      simp [purgeStagedPackets, getPeer, getDev, hd, hp, setPeer, modifyDev] at run
      rcases run with ⟨rfl, rfl⟩
      simpa [retryAt, peerAt, hd, hp, retryView] using pre

theorem retransmitGiveUp_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun g => ⌜retryAt g pid = some n⌝⦄ retransmitGiveUp pid
      ⦃⇓? _ g => ⌜retryAt g pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let P : WGWorld → Prop := fun g => retryAt g pid = some n
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient result final after pre run).1
  have hbranch (value : Bool) : Ensures (branch .retransmitZeroKeyNotPending value) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .retransmitZeroKeyNotPending value) P)
  change Ensures (do
    delTimer pid .sendKeepalive
    purgeStagedPackets pid
    let p ← getPeer pid
    let clear ← branch .retransmitZeroKeyNotPending !(p.timerPending .zeroKeyMaterial)
    if clear then do
      let _ ← modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
      pure ()
    else pure ()) P (fun _ => P)
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (delKeepalive_retryView pid n)) ?_
  intro ignored
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (purge_retryView pid n)) ?_
  intro ignored
  refine ensures_bind _ _ hread ?_
  intro p
  refine ensures_bind _ _ (hbranch _) ?_
  intro clear
  cases clear with
  | false => intro g ambient result final after pre run; cases run; exact pre
  | true =>
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (modZero_retryView .timerJiffiesRetransmitZeroKey pid ZERO_KEY_MATERIAL_TICKS n)) ?_
    intro ignored g ambient result final after pre run
    cases run
    exact pre


end Leanux.Proofs.WG.TimerDiscipline
