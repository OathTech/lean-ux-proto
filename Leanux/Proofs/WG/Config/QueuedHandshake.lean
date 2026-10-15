import Leanux.Proofs.WG.Config.KeyInstall

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem recordQueued_kernel (P : Kernel → Prop) (worker : Worker) (pid : PeerId) :
    ⦃fun w => ⌜P w.k⌝⦄ recordQueued worker pid ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hh := hidden_kernel_spec P
  mvcgen [recordQueued, hh]

theorem peerGet_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜w.k.wg = some (withPeer d pid { p with refcount := p.refcount + 1 }) ∧ 0 < p.refcount⌝⦄ := by
  mvcgen [peerGet, requireNotPending, refcountInc, branch, branchCmp,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer]
  all_goals omega

def queuedAfterClock (pid : PeerId) (p : Peer) (now : Int64) : M Unit := do
  let lhs := p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64
  if ← branchCmp .queuedNotExpired (!(lhs ≤ now)) lhs.toInt now.toInt then return
  if ← branch .queuedDead p.isDead then return
  peerGet pid
  if ← branch .queuedAlreadyQueued p.handshakePending then
    peerPut (some pid)
    return
  setPeer pid { (← getPeer pid) with handshakePending := true }
  recordQueued .sendWorker pid
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue ++ [pid] }
  modify fun w => { w with queuedThisCall := pid :: w.queuedThisCall }

def queuedDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  if !(p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now) || p.isDead then d
  else
    let acquired := withPeer d pid { p with refcount := p.refcount + 1 }
    if p.handshakePending then
      withPeer acquired pid p
    else
      let pending := withPeer acquired pid { p with refcount := p.refcount + 1, handshakePending := true }
      { pending with sendWorkQueue := pending.sendWorkQueue ++ [pid] }

theorem queuedAfterClock_exact (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p) :
    Ensures (queuedAfterClock pid p now) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (queuedDevice d pid p now)) := by
  have hg := peerGet_exact pid d p resident
  have hp :
      ⦃fun w => ⌜w.k.wg = some (withPeer d pid { p with refcount := p.refcount + 1 }) ∧ 0 < p.refcount⌝⦄
      peerPut (some pid)
      ⦃⇓? _ w => ⌜w.k.wg = some (withPeer (withPeer d pid { p with refcount := p.refcount + 1 }) pid p)⌝⦄ := by
    intro w ⟨hw, live⟩
    simpa using peerPut_retained pid
      (withPeer d pid { p with refcount := p.refcount + 1 })
      { p with refcount := p.refcount + 1 } (by simp [withPeer]) (by simp; omega) w hw
  have hq := recordQueued_kernel
    (fun k => k.wg = some (withPeer (withPeer d pid { p with refcount := p.refcount + 1 }) pid
      { p with refcount := p.refcount + 1, handshakePending := true })) .sendWorker pid
  rw [ensures_iff]
  by_cases expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now
  all_goals by_cases dead : p.isDead = true
  all_goals by_cases pending : p.handshakePending = true
  all_goals simp [queuedAfterClock, queuedDevice, branch, branchCmp, expired, dead, pending, bind_assoc]
  all_goals mvcgen -trivial [getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    invariant, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [queuedDevice, withPeer]
  all_goals subst_vars
  all_goals first
    | exact hp _ (by exact (show _ ∧ _ from by assumption).1)
    | mvcgen -trivial [hq, modifyDev, modifyK, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [withPeer]

def queuedReadPrefix (pid : PeerId) : M Peer := do
  requireNotPending pid "queueing a handshake"
  if ← branch .queuedNotRetry true then
    setPeer pid { (← getPeer pid) with timerHandshakeAttempts := 0 }
  getPeer pid

theorem sendQueued_clock_factor (pid : PeerId) :
    sendQueuedHandshakeInitiation pid false = (do
      let p ← queuedReadPrefix pid
      let now ← hiddenClock64 .birthdateExpired
      queuedAfterClock pid p now) := by
  simp [sendQueuedHandshakeInitiation, queuedReadPrefix, queuedAfterClock,
    branchExpired, birthdateTest, branch, bind_assoc]

theorem queuedReadPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (queuedReadPrefix pid) (fun w => w.k.wg = some d)
      (fun result w => result = { p with timerHandshakeAttempts := 0 } ∧
        w.k.wg = some (withPeer d pid { p with timerHandshakeAttempts := 0 })) := by
  rw [returns_iff]
  mvcgen [queuedReadPrefix, requireNotPending, branch, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withPeer]
  all_goals subst_vars
  all_goals simp_all [withPeer]
  all_goals grind only

theorem sendQueued_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.k.wg = some d)
    (run : (sendQueuedHandshakeInitiation pid false).run w = .ok ((), v)) :
    ∃ now before after,
      (queuedReadPrefix pid).run w = .ok ({ p with timerHandshakeAttempts := 0 }, before) ∧
      (hiddenClock64 .birthdateExpired).run before = .ok (now, after) ∧
      v.k.wg = some (queuedDevice (withPeer d pid { p with timerHandshakeAttempts := 0 })
        pid { p with timerHandshakeAttempts := 0 } now) := by
  obtain ⟨result, before, hprefix, rfl, hdevice⟩ := queuedReadPrefix_returns pid d p resident w device
  rw [sendQueued_clock_factor, StateT.run_bind, hprefix] at run
  change ((hiddenClock64 .birthdateExpired).run before >>= fun out =>
    (queuedAfterClock pid { p with timerHandshakeAttempts := 0 } out.1).run out.2) = .ok ((), v) at run
  cases hclock : (hiddenClock64 .birthdateExpired).run before with
  | error err => rw [hclock] at run; cases run
  | ok pair =>
    obtain ⟨now, after⟩ := pair
    rw [hclock] at run
    have hafter := (ensures_iff _ _ _).mpr
      (hiddenClock64_kernel_spec (fun k => k.wg = some (withPeer d pid { p with timerHandshakeAttempts := 0 }))
        .birthdateExpired) before now after hdevice hclock
    exact ⟨now, before, after, hprefix, hclock,
      queuedAfterClock_exact pid (withPeer d pid { p with timerHandshakeAttempts := 0 })
        { p with timerHandshakeAttempts := 0 } now (by simp [withPeer]) after () v hafter run⟩

theorem sendQueued_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (sendQueuedHandshakeInitiation pid false) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some
        (queuedDevice (withPeer d pid { p with timerHandshakeAttempts := 0 })
          pid { p with timerHandshakeAttempts := 0 } now)) := by
  intro w ret v hp hr
  cases ret
  obtain ⟨now, before, after, _, _, result⟩ := sendQueued_clock pid d p resident w v hp hr
  exact ⟨now, result⟩

end Leanux.Proofs.WG.Config
