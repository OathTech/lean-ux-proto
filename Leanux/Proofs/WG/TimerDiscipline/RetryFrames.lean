import Leanux.Proofs.WG.TimerDiscipline.RetryBaseSource
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
    ⦃fun w => ⌜retryAt w pid = some n⌝⦄ sendQueuedHandshakeInitiation pid true
      ⦃⇓? _ w => ⌜retryAt w pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      have hn : retryView p = n := by simpa [retryAt, peerAt, hd, hp] using pre
      obtain ⟨now, device⟩ := sendQueuedRetry_exact pid d p hp w result final hd run
      simpa [retryAt, peerAt, device, hn] using queuedDevice_retryView pid d p now hp

theorem clearEndpoint_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun w => ⌜retryAt w pid = some n⌝⦄ clearPeerEndpointSrc pid
      ⦃⇓? _ w => ⌜retryAt w pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      have hn : retryView p = n := by simpa [retryAt, peerAt, hd, hp] using pre
      obtain ⟨out, reset, device, _, peer, _⟩ :=
        clearEndpointSource_exact pid d p hp w result final hd run
      simpa [retryAt, peerAt, device, peer, clearedSource, retryView] using hn

theorem modZero_retryView (site : HiddenSite) (pid : PeerId) (delay : Nat) (n : RetryView) :
    ⦃fun w => ⌜retryAt w pid = some n⌝⦄ modPeerTimer site pid .zeroKeyMaterial delay
      ⦃⇓? _ w => ⌜retryAt w pid = some n⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  cases hd : w.k.wg with
  | none => simp [retryAt, peerAt, hd] at pre
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [retryAt, peerAt, hd, hp] at pre
    | some p =>
      have hn : retryView p = n := by simpa [retryAt, peerAt, hd, hp] using pre
      obtain ⟨guard, effect⟩ := modPeerTimer_effect site pid .zeroKeyMaterial delay d p hp
        w result final hd run
      cases result with
      | false =>
        change peerAt final pid = some p at effect
        simpa [retryAt, effect] using hn
      | true =>
        obtain ⟨expiry, peer⟩ := effect
        simpa [retryAt, peer, retryView, Peer.setTimer] using hn

theorem delKeepalive_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun w => ⌜retryAt w pid = some n⌝⦄ delTimer pid .sendKeepalive
      ⦃⇓? _ w => ⌜retryAt w pid = some n⌝⦄ := by
  mvcgen [delTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [retryAt, retryView, peerAt, Peer.setTimer]
  all_goals grind only

theorem purge_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun w => ⌜retryAt w pid = some n⌝⦄ purgeStagedPackets pid
      ⦃⇓? _ w => ⌜retryAt w pid = some n⌝⦄ := by
  mvcgen [purgeStagedPackets, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [retryAt, retryView, peerAt]
  all_goals grind only

theorem retransmitGiveUp_retryView (pid : PeerId) (n : RetryView) :
    ⦃fun w => ⌜retryAt w pid = some n⌝⦄ retransmitGiveUp pid
      ⦃⇓? _ w => ⌜retryAt w pid = some n⌝⦄ := by
  have hd := delKeepalive_retryView pid n
  have hp := purge_retryView pid n
  have hm := modZero_retryView .timerJiffiesRetransmitZeroKey pid ZERO_KEY_MATERIAL_TICKS n
  have hm' := map_result_spec (fun _ : Bool => PUnit.unit) _ _ _ hm
  simp only [retransmitGiveUp, Functor.discard, Functor.mapConst]
  mvcgen [getPeer, getDev, getK, invariant, branch, hd, hp, hm']
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals exact hm' _ (by assumption)

end Leanux.Proofs.WG.TimerDiscipline
