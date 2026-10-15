import Leanux.Proofs.WG.TimerDiscipline.Arming
import Leanux.Proofs.WG.Config.QueuedHandshake
import Leanux.Proofs.WG.Config.EndpointSources

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Retry variant of Config.queuedReadPrefix: retain the original false
queuedNotRetry decision and do not reset the attempt counter. -/
def retryReadPrefix (pid : PeerId) : M Peer := do
  requireNotPending pid "queueing a handshake"
  _ ← branch .queuedNotRetry false
  getPeer pid

theorem sendQueuedRetry_factor (pid : PeerId) :
    sendQueuedHandshakeInitiation pid true = (do
      let p ← retryReadPrefix pid
      let now ← hiddenClock64 .birthdateExpired
      queuedAfterClock pid p now) := by
  simp [sendQueuedHandshakeInitiation, retryReadPrefix, queuedAfterClock,
    branchExpired, birthdateTest, branch, bind_assoc]

theorem retryReadPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (retryReadPrefix pid) (fun w => w.k.wg = some d)
      (fun result w => result = p ∧ w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [retryReadPrefix, requireNotPending, branch, getPeer, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

theorem sendQueuedRetry_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (sendQueuedHandshakeInitiation pid true) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (queuedDevice d pid p now)) := by
  intro w ret v hp run
  cases ret
  obtain ⟨result, before, hprefix, value, hdevice⟩ := retryReadPrefix_returns pid d p resident w hp
  subst result
  rw [sendQueuedRetry_factor, StateT.run_bind, hprefix] at run
  change ((hiddenClock64 .birthdateExpired).run before >>= fun out =>
    (queuedAfterClock pid p out.1).run out.2) = .ok ((), v) at run
  cases hclock : (hiddenClock64 .birthdateExpired).run before with
  | error err => rw [hclock] at run; cases run
  | ok pair =>
    obtain ⟨now, after⟩ := pair
    rw [hclock] at run
    have hafter := (ensures_iff _ _ _).mpr
      (hiddenClock64_kernel_spec (fun k => k.wg = some d) .birthdateExpired)
      before now after hdevice hclock
    exact ⟨now, queuedAfterClock_exact pid d p now resident after () v hafter run⟩

abbrev RetryView := Nat × Nat × Option UInt64

def retryView (p : Peer) : RetryView :=
  (p.internalId, p.timerHandshakeAttempts, p.timerRetransmitHandshake)

def retryAt (w : World) (pid : PeerId) : Option RetryView :=
  (peerAt w pid).map retryView

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

def nextAttempts (attempts : Nat) : Nat :=
  if attempts > MAX_TIMER_HANDSHAKES then attempts else attempts + 1

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

def retransmitGiveUp (pid : PeerId) : M Unit := do
  delTimer pid .sendKeepalive
  purgeStagedPackets pid
  if ← branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) then
    discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

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

theorem expiredRetransmit_source (pid : PeerId) :
    expiredRetransmitHandshake pid = (do
      let attempts := (← getPeer pid).timerHandshakeAttempts
      if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
        retransmitGiveUp pid
      else
        let p ← getPeer pid
        setPeer pid { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 }
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) := rfl

theorem expiredRetransmit_retryView (pid : PeerId) (identity attempts : Nat)
    (timer : Option UInt64) :
    Ensures (expiredRetransmitHandshake pid)
      (fun w => retryAt w pid = some (identity, attempts, timer))
      (fun _ w => retryAt w pid = some (identity, nextAttempts attempts, timer)) := by
  have hq := sendQueuedRetry_retryView pid (identity, attempts + 1, timer)
  have hc := clearEndpoint_retryView pid (identity, attempts + 1, timer)
  have hg := retransmitGiveUp_retryView pid (identity, attempts, timer)
  rw [expiredRetransmit_source, ensures_iff]
  mvcgen [getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branchCmp, invariant, hq, hc, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [retryAt, retryView, peerAt, nextAttempts]
  all_goals grind only

end Leanux.Proofs.WG.TimerDiscipline
