import Leanux.Proofs.WG.Config.ExpiryEffects

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def expiryReadPrefix (pid : PeerId) : M Unit := do
  requireNotPending pid "clearing the handshake"
  handshakeClear pid

def expiryZeroDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  withPeer { d with indexTable := d.indexTable.filter fun e => !(e.owner == .handshake pid) }
    pid (zeroedHandshake p)

def expiryAfterClock (pid : PeerId) (now : Int64) : M Unit := do
  setPeer pid { (← getPeer pid) with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }
  expiryTailSource pid

theorem expireCurrent_clock_factor (pid : PeerId) :
    expireCurrentPeerKeypairs pid = (do
      expiryReadPrefix pid
      let now ← hiddenClock64 .resetLastSent
      expiryAfterClock pid now) := by
  rw [expireCurrent_source]
  simp [expiryHeadSource, expiryReadPrefix, expiryAfterClock, resetLastSentHandshake, bind_assoc]

theorem expiryReadPrefix_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expiryReadPrefix pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (expiryZeroDevice d pid p)) := by
  rw [ensures_iff]
  noise_vcgen [expiryReadPrefix, requireNotPending, handshakeClear, IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, indexRemove,
    _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry, handshakeZero,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [expiryZeroDevice, zeroedHandshake, withPeer]
  all_goals subst_vars
  all_goals simp_all
  all_goals grind only

theorem expiryAfterClock_exact (pid : PeerId) (d : Device) (p : Peer) (now : Int64) :
    Ensures (expiryAfterClock pid now) (fun w => w.k.wg = some (expiryZeroDevice d pid p))
      (fun _ w => w.k.wg = some (expiredDevice d pid p now)) := by
  let reset : Peer := { zeroedHandshake p with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }
  have hresident : (expiryHeadDevice d pid p now).peers[pid]? = some reset := by
    simp [expiryHeadDevice, withPeer, reset]
  have ht := (ensures_iff _ _ _).mp (expiryTail_exact pid (expiryHeadDevice d pid p now) reset hresident)
  rw [ensures_iff]
  mvcgen [expiryAfterClock, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [expiryZeroDevice, expiryHeadDevice, expiredDevice, reset, zeroedHandshake, withPeer]
  all_goals grind only

theorem expireCurrent_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.k.wg = some d)
    (run : (expireCurrentPeerKeypairs pid).run w = .ok ((), v)) :
    ∃ now before after,
      (expiryReadPrefix pid).run w = .ok ((), before) ∧
      (hiddenClock64 .resetLastSent).run before = .ok (now, after) ∧
      v.k.wg = some (expiredDevice d pid p now) := by
  rw [expireCurrent_clock_factor, StateT.run_bind] at run
  cases hprefix : (expiryReadPrefix pid).run w with
  | error err => rw [hprefix] at run; cases run
  | ok pair =>
    obtain ⟨u, before⟩ := pair
    cases u
    have hdevice := expiryReadPrefix_exact pid d p resident w () before device hprefix
    rw [hprefix] at run
    change ((hiddenClock64 .resetLastSent).run before >>= fun out =>
      (expiryAfterClock pid out.1).run out.2) = .ok ((), v) at run
    cases hclock : (hiddenClock64 .resetLastSent).run before with
    | error err => rw [hclock] at run; cases run
    | ok pair =>
      obtain ⟨now, after⟩ := pair
      rw [hclock] at run
      have hafter := (ensures_iff _ _ _).mpr
        (hiddenClock64_kernel_spec (fun k => k.wg = some (expiryZeroDevice d pid p)) .resetLastSent)
        before now after hdevice hclock
      exact ⟨now, before, after, rfl, hclock, expiryAfterClock_exact pid d p now after () v hafter run⟩

end Leanux.Proofs.WG.Config
