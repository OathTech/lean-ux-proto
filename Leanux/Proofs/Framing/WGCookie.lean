import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.WGOwned
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Receive

/-! Canonical original cookie frames. The projection omits only the device
cookie secret/birthdate and both ratelimiter tables. It retains device presence,
complete resident stores, every allocation frontier, and all eleven WG-owned
observations outside that mask. Source inspection establishes that these four helpers do
not dereference resident peers, keypairs or packets. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def cookieDevice (d : Device) : Device :=
  {d with cookieSecret := [], cookieSecretBirthdate := 0}

def cookieView (g : WGWorld) : WGOwnedView :=
  {wgOwnedView g with
    dev := g.dev.map cookieDevice
    ratelimiter := {g.ratelimiter with table := [], table6 := []}}

abbrev SameCookie (a : WG.M α) := SameView cookieView a

theorem modifyDev_cookie_spec (P : WGOwnedView → Prop) (f : Device → Device)
    (hf : ∀ d, cookieDevice (f d) = cookieDevice d) :
    ⦃fun w => ⌜P (cookieView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (cookieView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [cookieView, wgOwnedView, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem makeCookie_sameCookie (src : SkbSource) : SameCookie (makeCookie src) := by
  apply SameView.of_wp
  intro initial
  have he := fun d b n => ((branchExpired_sameWGWorld d b n).factor cookieView).wp (fun s => s = initial)
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g => ⌜cookieView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜cookieView g = initial⌝⦄ := hoare_liftAmbient a _
  have hm := modifyDev_cookie_spec (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, makeCookie, getDev, branch, invariant,
    hiddenClock64, hidden, he, ha, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cookieView, wgOwnedView, wgStoreView, cookieDevice]

theorem ratelimiterAllow_sameCookie (src : SkbSource) : SameCookie (ratelimiterAllow src) := by
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g => ⌜cookieView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜cookieView g = initial⌝⦄ := hoare_liftAmbient a _
  have hm (f : WGWorld → WGWorld)
      (hf : ∀ g, cookieView (f g) = cookieView g) :
      ⦃fun g => ⌜cookieView g = initial⌝⦄ (modify f : WG.M Unit)
      ⦃⇓? _ g => ⌜cookieView g = initial⌝⦄ := by
    apply hoare_modify
    intro g h
    simpa only [hf] using h
  mvcgen [-Std.Do.Spec.monadLift_StateT, ratelimiterAllow, branch, branchCmp,
    unsupported, invariant, hiddenClock, hiddenAlloc, ha, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals try split
  all_goals simp_all [cookieView, wgOwnedView, wgStoreView, cookieDevice]

theorem cookieMessageCreate_sameCookie (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    SameCookie (cookieMessageCreate index src mac1) := by
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g => ⌜cookieView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜cookieView g = initial⌝⦄ := hoare_liftAmbient a _
  have hm := (makeCookie_sameCookie src).wp (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, cookieMessageCreate, getDev, invariant, hidden, ha, hm]

theorem cookieValidatePacket_sameCookie (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    SameCookie (cookieValidatePacket msg src checkCookie) := by
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g => ⌜cookieView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜cookieView g = initial⌝⦄ := hoare_liftAmbient a _
  have hm := (makeCookie_sameCookie src).wp (fun s => s = initial)
  have hr := (ratelimiterAllow_sameCookie src).wp (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, cookieValidatePacket, getDev, invariant, branch, ha, hm, hr]

end Leanux.Proofs.Framing
