import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.Tools
import Leanux.WG.Receive

/-! Canonical original cookie frames. The projection omits only the device
cookie secret/birthdate and both ratelimiter tables. It retains device presence,
complete resident stores, every allocation frontier, and all other Kernel
fields. Source inspection separately establishes that these four helpers do
not dereference resident peers, keypairs or packets. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def cookieDevice (d : Device) : Device :=
  {d with cookieSecret := [], cookieSecretBirthdate := 0}

def cookieKernel (k : Kernel) : Kernel :=
  {k with
    wg := k.wg.map cookieDevice
    ratelimiter := {k.ratelimiter with table := [], table6 := []}}

def cookieKernelView (w : World) : Kernel := cookieKernel w.k

abbrev SameCookieKernel (a : M α) := SameView cookieKernelView a

theorem modifyDev_cookie_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, cookieDevice (f d) = cookieDevice d) :
    ⦃fun w => ⌜P (cookieKernelView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (cookieKernelView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [cookieKernelView, cookieKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem modifyK_cookie_spec (P : Kernel → Prop) (f : Kernel → Kernel)
    (hf : ∀ k, cookieKernel (f k) = cookieKernel k) :
    ⦃fun w => ⌜P (cookieKernelView w)⌝⦄ modifyK f
    ⦃⇓? _ w => ⌜P (cookieKernelView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [cookieKernelView, modifyK, hf] using hp

theorem makeCookie_sameCookieKernel (src : SkbSource) : SameCookieKernel (makeCookie src) := by
  apply SameView.of_wp
  intro initial
  have he := fun d b n => (SameView.of_sameKernel cookieKernel (branchExpired_sameKernel d b n)).wp (fun s => s = initial)
  have hc := fun site => (SameView.of_sameKernel cookieKernel (hiddenClock64_sameKernel site)).wp (fun s => s = initial)
  have hh := fun site => (SameView.of_sameKernel cookieKernel (hidden_sameKernel site)).wp (fun s => s = initial)
  have hm := modifyDev_cookie_spec (fun s => s = initial)
  mvcgen [makeCookie, getDev, getK, branch, invariant, he, hc, hh, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cookieKernelView, cookieKernel, cookieDevice]

theorem ratelimiterAllow_sameCookieKernel (src : SkbSource) : SameCookieKernel (ratelimiterAllow src) := by
  apply SameView.of_wp
  intro initial
  have hc := fun site => (SameView.of_sameKernel cookieKernel (hiddenClock_sameKernel site)).wp (fun s => s = initial)
  have he := fun site => (SameView.of_sameKernel cookieKernel (hiddenAlloc_sameKernel site)).wp (fun s => s = initial)
  have hm := modifyK_cookie_spec (fun s => s = initial)
  mvcgen [ratelimiterAllow, getK, branch, branchCmp, unsupported, invariant, hc, he, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cookieKernelView, cookieKernel, cookieDevice]

theorem cookieMessageCreate_sameCookieKernel (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    SameCookieKernel (cookieMessageCreate index src mac1) := by
  apply SameView.of_wp
  intro initial
  have hh := fun site => (SameView.of_sameKernel cookieKernel (hidden_sameKernel site)).wp (fun s => s = initial)
  have hm := (makeCookie_sameCookieKernel src).wp (fun s => s = initial)
  mvcgen [cookieMessageCreate, getDev, getK, invariant, hh, hm]

theorem cookieValidatePacket_sameCookieKernel (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    SameCookieKernel (cookieValidatePacket msg src checkCookie) := by
  apply SameView.of_wp
  intro initial
  have hm := (makeCookie_sameCookieKernel src).wp (fun s => s = initial)
  have hr := (ratelimiterAllow_sameCookieKernel src).wp (fun s => s = initial)
  mvcgen [cookieValidatePacket, getDev, getK, invariant, branch, hm, hr]

end Leanux.Proofs.Framing
