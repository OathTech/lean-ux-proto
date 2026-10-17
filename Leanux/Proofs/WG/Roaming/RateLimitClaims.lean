import Leanux.Proofs.WG.Roaming.RateLimitModel
import Leanux.Proofs.WG.Roaming.RateLimitFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- The actual non-cookie receiver retains all peers and their endpoints after
an observed rate-limit refusal. This is normal-return preservation, with no
load, MAC, clock, allocation, source-family or peer-residency premise. -/
theorem receiveHandshakePacket_ratelimited (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot)
    (noncookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE) :
    Campaign2.Product.Ensures (observedRateLimitHandshake msg src) (fun s => s = entry)
      (fun result final => RateLimitRejectionObservation entry result.1 final) := by
  unfold observedRateLimitHandshake
  apply TimerDiscipline.observed_effect
  intro initial result final pre run
  subst entry
  change (((receiveHandshakePacket msg src).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
    Except.ok (value, {initial with wg := current, ambient := inputs})) = _ at run
  cases native : ((receiveHandshakePacket msg src).run initial.wg).run initial.ambient with
  | error stop => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, after⟩ := pair
    rw [native] at run
    cases run
    have factored := native
    rw [receiveHandshakePacket_rateLimit_factor msg src noncookie] at factored
    change (((rateLimitPrefix msg src).run initial.wg).run initial.ambient >>= fun ((input, middle), inputs) =>
      ((rateLimitSuffix msg src input).run middle).run inputs) = _ at factored
    cases prefixRun : ((rateLimitPrefix msg src).run initial.wg).run initial.ambient with
    | error stop => rw [prefixRun] at factored; cases factored
    | ok pair =>
      obtain ⟨⟨⟨loaded,mac⟩,middle⟩,inputs⟩ := pair
      rw [prefixRun] at factored
      let prefixWorld := {initial with wg := middle, ambient := inputs}
      have prefixLift : (liftWG (rateLimitPrefix msg src)).run initial =
          .ok ((loaded,mac), prefixWorld) := by
        change (((rateLimitPrefix msg src).run initial.wg).run initial.ambient >>= _) = _
        rw [prefixRun]
        rfl
      refine ⟨loaded,mac,Campaign2.Product.snapshot prefixWorld,
        TimerDiscipline.observe_ok prefixLift, ?_⟩
      intro refused
      subst mac
      have sameState := rateLimitSuffix_ratelimited msg src loaded middle
        middle inputs () current after rfl factored
      subst current
      have peers := rateLimitPrefix_peers msg src initial.wg initial.wg initial.ambient (loaded,.ratelimited)
        middle inputs rfl prefixRun
      refine ⟨peers, ?_⟩
      intro pid
      cases beforeDevice : initial.wg.dev <;> cases afterDevice : middle.dev
      all_goals simp only [beforeDevice,afterDevice,Option.map_none,Option.map_some,Option.some.injEq] at peers
      all_goals try { contradiction }
      all_goals simp only [remoteAt,Campaign2.Snapshot.peerAt,Campaign2.Product.snapshot,
        Campaign2.snapshot,Campaign2.core,beforeDevice,afterDevice,Option.bind_none,Option.bind_some]
      all_goals first | rfl | rw [peers]

end Leanux.Proofs.WG.Roaming
