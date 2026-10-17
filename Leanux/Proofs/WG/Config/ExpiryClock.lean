import Leanux.Proofs.WG.Config.ExpiryEffects

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def expiryAfterClock (pid : PeerId) (now : Int64) : WG.M Unit := do
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

theorem expiryAfterClock_exact (pid : PeerId) (d : Device) (p : Peer) (now : Int64) :
    Ensures (expiryAfterClock pid now) (fun w => w.dev = some (expiryZeroDevice d pid p))
      (fun _ w => w.dev = some (expiredDevice d pid p now)) := by
  let reset : Peer := {zeroedHandshake p with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64}
  have hresident : (expiryHeadDevice d pid p now).peers[pid]? = some reset := by
    simp [expiryHeadDevice, withPeer, reset]
  have hset : Ensures (do setPeer pid { (← getPeer pid) with
      lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 })
      (fun g => g.dev = some (expiryZeroDevice d pid p))
      (fun _ g => g.dev = some (expiryHeadDevice d pid p now)) := by
    intro g ambient result final after device run
    simp [getPeer, getDev, device, expiryZeroDevice, withPeer, setPeer, modifyDev] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  unfold expiryAfterClock
  rw [← bind_assoc]
  refine ensures_bind _ _ hset ?_
  intro _ g ambient result final after device run
  have post := expiryTail_exact pid (expiryHeadDevice d pid p now) reset hresident
    g ambient result final after device run
  simpa [expiredDevice, reset, zeroedHandshake] using post

theorem expireCurrent_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : WGWorld) (ambient tail : Ambient)
    (device : w.dev = some d)
    (run : ((expireCurrentPeerKeypairs pid).run w).run ambient = .ok (((), v), tail)) :
    ∃ now before beforeAmbient after afterAmbient,
      ((expiryReadPrefix pid).run w).run ambient = .ok (((), before), beforeAmbient) ∧
      ((hiddenClock64 .resetLastSent : WG.M Int64).run before).run beforeAmbient =
        .ok ((now, after), afterAmbient) ∧
      v.dev = some (expiredDevice d pid p now) := by
  rw [expireCurrent_clock_factor] at run
  change (((expiryReadPrefix pid).run w).run ambient >>= fun ((_, before), middle) =>
    (((do let now ← hiddenClock64 .resetLastSent
          expiryAfterClock pid now) : WG.M Unit).run before).run middle) =
      .ok (((), v), tail) at run
  cases hprefix : ((expiryReadPrefix pid).run w).run ambient with
  | error err => rw [hprefix] at run; cases run
  | ok pair =>
    obtain ⟨⟨u, before⟩, beforeAmbient⟩ := pair
    cases u
    have hdevice := expiryReadPrefix_exact pid d p resident
      w ambient () before beforeAmbient device hprefix
    rw [hprefix] at run
    change (((hiddenClock64 .resetLastSent : WG.M Int64).run before).run beforeAmbient >>= fun ((now, after), middle) =>
      ((expiryAfterClock pid now).run after).run middle) = .ok (((), v), tail) at run
    cases hclock : ((hiddenClock64 .resetLastSent : WG.M Int64).run before).run beforeAmbient with
    | error err => rw [hclock] at run; cases run
    | ok pair =>
      obtain ⟨⟨now, after⟩, afterAmbient⟩ := pair
      rw [hclock] at run
      have hafter := (ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .resetLastSent)
          (fun g : WGWorld => g.dev = some (expiryZeroDevice d pid p)))
        before beforeAmbient now after afterAmbient hdevice hclock
      exact ⟨now, before, beforeAmbient, after, afterAmbient, rfl, hclock,
        expiryAfterClock_exact pid d p now after afterAmbient () v tail hafter run⟩

end Leanux.Proofs.WG.Config
