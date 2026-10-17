import Leanux.Proofs.WG.Roaming.RateLimitSource
import Leanux.Proofs.WG.Roaming.InvalidMac1Frames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Narrow local variant of campaign 1's Framing.makeCookie_sameCookie:
retain the complete optional peer map while cookie-secret rotation remains active. -/
theorem makeCookie_sameCookie_variant (src : SkbSource) (before : WGWorld) :
    Ensures (makeCookie src)
      (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
      (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers)) := by
  let P : WGWorld → Prop := fun g => g.dev.map (·.peers) = before.dev.map (·.peers)
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) P)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes P (fun _ => P))
      (hn : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  have hmodify (birthdate : Int64) (secret : List UInt8) :
      Ensures (modifyDev fun d => {d with cookieSecretBirthdate := birthdate, cookieSecret := secret})
        P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    simpa only [P, modifyDev, Option.map_map, Function.comp_def] using pre
  change Ensures _ P (fun _ => P)
  unfold makeCookie branchExpired birthdateTest
  simp only [bind_assoc, pure_bind]
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hambient _
    | exact hbranch _ _
    | exact hcmp _ _ _ _
    | exact hmodify _ _
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)

/-- Narrow local variant of campaign 1's Framing.ratelimiterAllow_sameCookie:
rate-limit table changes and refusal paths do not write resident peers. -/
theorem ratelimiterAllow_sameCookie_variant (src : SkbSource) (before : WGWorld) :
    Ensures (ratelimiterAllow src)
      (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
      (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers)) := by
  let P : WGWorld → Prop := fun g => g.dev.map (·.peers) = before.dev.map (·.peers)
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) P)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes P (fun _ => P))
      (hn : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  have hget : Ensures (get : WG.M WGWorld) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hmodify (f : WGWorld → WGWorld) (same : ∀ g, (f g).dev = g.dev) :
      Ensures (modify f : WG.M Unit) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    change (f g).dev.map (·.peers) = before.dev.map (·.peers)
    rw [same]
    exact pre
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; simp [invariant, AmbientM.invariant] at run; cases run
  have hunsupported {α : Type} (message : String) : Ensures (unsupported message : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; simp [unsupported, AmbientM.unsupported] at run; cases run
  change Ensures _ P (fun _ => P)
  unfold ratelimiterAllow
  repeat' first
    | exact hpure _
    | exact hget
    | exact hambient _
    | exact hbranch _ _
    | exact hcmp _ _ _ _
    | exact hstop _
    | exact hunsupported _
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
  all_goals rename_i family
  all_goals rcases family with ⟨v6, ip⟩
  all_goals cases v6
  all_goals dsimp only
  all_goals
    repeat' first
      | exact hpure _
      | exact hget
      | exact hambient _
      | exact hbranch _ _
      | exact hcmp _ _ _ _
      | exact hstop _
      | exact hunsupported _
      | exact hmodify _ (fun _ => rfl)
      | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)
      | split

/-- Narrow local variant of campaign 1's Framing.cookieValidatePacket_sameCookie.
No MAC, load, family, clock or allocation readiness is assumed. -/
theorem cookieValidatePacket_sameCookie_variant (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) (before : WGWorld) :
    Ensures (cookieValidatePacket msg src checkCookie)
      (fun g => g.dev.map (·.peers) = before.dev.map (·.peers))
      (fun _ g => g.dev.map (·.peers) = before.dev.map (·.peers)) := by
  let P : WGWorld → Prop := fun g => g.dev.map (·.peers) = before.dev.map (·.peers)
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes P (fun _ => P))
      (hn : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  have hc := makeCookie_sameCookie_variant src before
  have hr := ratelimiterAllow_sameCookie_variant src before
  change Ensures _ P (fun _ => P)
  unfold cookieValidatePacket
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hbranch _ _
    | exact hc
    | exact hr
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)

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
