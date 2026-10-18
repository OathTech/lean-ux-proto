import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.WG.Roaming.RateLimitSource
import Leanux.Proofs.WG.Roaming.InvalidMac1Frames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Projection of landed campaign 1's Framing.makeCookie_sameCookie:
retain the complete optional peer map while cookie-secret rotation remains active. -/
theorem makeCookie_sameCookie_variant (src : SkbSource) (before : WGWorld) :
    Ensures (makeCookie src)
      (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
      (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers)) := by
  refine (Noise.ensures_iff (makeCookie src)
    (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
    (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers))).mpr ?_
  simpa [Leanux.Proofs.Framing.cookieView, Leanux.Proofs.Framing.cookieDevice,
    Option.map_map, Function.comp_def] using
    (Leanux.Proofs.Framing.makeCookie_sameCookie src).wp
      (fun v => v.dev.map (·.peers) = before.dev.map (·.peers))

/-- Projection of landed campaign 1's Framing.ratelimiterAllow_sameCookie:
rate-limit table changes and refusal paths do not write resident peers. -/
theorem ratelimiterAllow_sameCookie_variant (src : SkbSource) (before : WGWorld) :
    Ensures (ratelimiterAllow src)
      (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
      (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers)) := by
  refine (Noise.ensures_iff (ratelimiterAllow src)
    (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
    (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers))).mpr ?_
  simpa [Leanux.Proofs.Framing.cookieView, Leanux.Proofs.Framing.cookieDevice,
    Option.map_map, Function.comp_def] using
    (Leanux.Proofs.Framing.ratelimiterAllow_sameCookie src).wp
      (fun v => v.dev.map (·.peers) = before.dev.map (·.peers))

/-- Projection of landed campaign 1's Framing.cookieValidatePacket_sameCookie.
No MAC, load, family, clock or allocation readiness is assumed. -/
theorem cookieValidatePacket_sameCookie_variant (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) (before : WGWorld) :
    Ensures (cookieValidatePacket msg src checkCookie)
      (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
      (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers)) := by
  refine (Noise.ensures_iff (cookieValidatePacket msg src checkCookie)
    (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
    (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers))).mpr ?_
  simpa [Leanux.Proofs.Framing.cookieView, Leanux.Proofs.Framing.cookieDevice,
    Option.map_map, Function.comp_def] using
    (Leanux.Proofs.Framing.cookieValidatePacket_sameCookie msg src checkCookie).wp
      (fun v => v.dev.map (·.peers) = before.dev.map (·.peers))

/-- A rate-limit verdict drops the packet before either handshake consumer,
setter or cookie-reply path. Only Ambient decision records change. -/
theorem rateLimitSuffix_ratelimited (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (initial : WGWorld) :
    Ensures (rateLimitSuffix msg src (loaded, .ratelimited)) (fun g => g = initial)
      (fun _ g => g = initial) := by
  intro g ambient result final after pre run
  subst g
  cases loaded <;>
    simp [rateLimitSuffix, WG.andM, WG.orM, branch, AmbientM.branch] at run
  all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; rfl

/-- Compose the actual load and cookie checks without changing the optional peer map. -/
theorem rateLimitPrefix_peers (msg : List UInt8) (src : SkbSource) (initial : WGWorld) :
    Ensures (rateLimitPrefix msg src)
      (fun g => g.dev.map (·.peers) = initial.dev.map (·.peers))
      (fun _ g => g.dev.map (·.peers) = initial.dev.map (·.peers)) := by
  let P : WGWorld → Prop := fun g => g.dev.map (·.peers) = initial.dev.map (·.peers)
  have loadFrame : Ensures responseLoad P (fun _ => P) := by
    intro g a value after b pre run
    change after.dev.map (·.peers) = initial.dev.map (·.peers)
    rw [responseLoad_device g.dev g a value after b rfl run]
    exact pre
  unfold rateLimitPrefix
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branch .hsCookie false) P)) ?_
  intro _
  refine ensures_bind _ _ loadFrame ?_
  intro loaded
  refine ensures_bind _ _ (cookieValidatePacket_sameCookie_variant msg src loaded initial) ?_
  intro mac g a result final after pre run
  cases run
  exact pre

end Leanux.Proofs.WG.Roaming
