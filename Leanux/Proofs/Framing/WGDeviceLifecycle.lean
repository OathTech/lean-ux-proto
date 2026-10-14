import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.Kernel
import Leanux.Proofs.Framing.Tools
import Leanux.WG.Device

/-! Canonical lifecycle leaf frames. Ratelimiter bookkeeping changes no device
or allocation frontier. Newlink initialization additionally changes only its
named device scalar fields; the final epoch assignment is proved separately.
These leaves do not dereference resident peers, keypairs or packets. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def ratelimiterKernel (k : Kernel) : Kernel := {k with ratelimiter := {}}
def ratelimiterKernelView (w : World) : Kernel := ratelimiterKernel w.k
abbrev SameRatelimiterKernel (a : M α) := SameView ratelimiterKernelView a

theorem mayHaveSlept_sameKernel : SameKernel mayHaveSlept := by
  intro w x v hr; cases hr; rfl

theorem retireDeviceUnits_sameKernel : SameKernel retireDeviceUnits := by
  intro w x v hr; cases hr; rfl

theorem ratelimiterInit_sameRatelimiterKernel : SameRatelimiterKernel ratelimiterInit := by
  apply SameView.of_wp
  intro initial
  have he := fun s => (SameView.of_sameKernel ratelimiterKernel (envOk_sameKernel s)).wp (fun v => v = initial)
  have hh := fun s => (SameView.of_sameKernel ratelimiterKernel (hidden_sameKernel s)).wp (fun v => v = initial)
  mvcgen [ratelimiterInit, he, hh, getK, modifyK, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ratelimiterKernelView, ratelimiterKernel]
  all_goals trivial

theorem gcEntries_sameRatelimiterKernel (work : Bool) : SameRatelimiterKernel (gcEntries work) := by
  apply SameView.of_wp
  intro initial
  have hc := fun s => (SameView.of_sameKernel ratelimiterKernel (hiddenClock_sameKernel s)).wp (fun v => v = initial)
  have hl (α β : Type) := list_view_spec ratelimiterKernelView (α := α) (β := β) (fun v => v = initial)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    gcEntries, hc, getK, modifyK, branch, unsupported]
  all_goals try exact ((⇓? _ w => ⌜ratelimiterKernelView w = initial⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ratelimiterKernelView, ratelimiterKernel]
  all_goals trivial

theorem ratelimiterUninit_sameRatelimiterKernel : SameRatelimiterKernel ratelimiterUninit := by
  apply SameView.of_wp
  intro initial
  have hg := fun b => (gcEntries_sameRatelimiterKernel b).wp (fun v => v = initial)
  have hm := (SameView.of_sameKernel ratelimiterKernel mayHaveSlept_sameKernel).wp (fun v => v = initial)
  have hs := fun sites => (SameView.of_sameKernel ratelimiterKernel (skipCut_sameKernel sites)).wp (fun v => v = initial)
  mvcgen [ratelimiterUninit, hg, hm, hs, getK, modifyK, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ratelimiterKernelView, ratelimiterKernel]
  all_goals trivial

def linkDevice (d : Device) : Device :=
  {d with creatingNet := false, deviceUpdateGen := 0, cookieSecret := [], cookieSecretBirthdate := 0, pubkeyHashKey := []}
def linkKernel (k : Kernel) : Kernel :=
  {k with ratelimiter := {}, wg := k.wg.map linkDevice}
def linkKernelView (w : World) : Kernel := linkKernel w.k
abbrev SameLinkKernel (a : M α) := SameView linkKernelView a

theorem ratelimiter_link (ha : SameRatelimiterKernel a) : SameLinkKernel a := by
  intro w x v hr
  have he := congrArg linkKernel (ha w x v hr)
  simpa [linkKernelView, linkKernel, ratelimiterKernelView, ratelimiterKernel] using he

theorem modifyDev_link_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, linkDevice (f d) = linkDevice d) :
    ⦃fun w => ⌜P (linkKernelView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (linkKernelView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [linkKernelView, linkKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem cookieCheckerInit_sameLinkKernel : SameLinkKernel cookieCheckerInit := by
  apply SameView.of_wp
  intro initial
  have hc := fun s => (SameView.of_sameKernel linkKernel (hiddenClock64_sameKernel s)).wp (fun v => v = initial)
  have hh := fun s => (SameView.of_sameKernel linkKernel (hidden_sameKernel s)).wp (fun v => v = initial)
  have hm := modifyDev_link_spec (fun s => s = initial)
  mvcgen [cookieCheckerInit, hc, hh, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [linkKernelView, linkKernel, linkDevice, Option.map_map, Function.comp_def]

theorem pubkeyHashtableAlloc_sameLinkKernel : SameLinkKernel pubkeyHashtableAlloc := by
  apply SameView.of_wp
  intro initial
  have he := fun s => (SameView.of_sameKernel linkKernel (envOk_sameKernel s)).wp (fun v => v = initial)
  have hh := fun s => (SameView.of_sameKernel linkKernel (hidden_sameKernel s)).wp (fun v => v = initial)
  have hm := modifyDev_link_spec (fun s => s = initial)
  mvcgen [pubkeyHashtableAlloc, he, hh, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [linkKernelView, linkKernel, linkDevice, Option.map_map, Function.comp_def]

/-- The full WG projection after masking only newlink initialization fields. -/
def linkView (w : World) : WGKernelView := WGKernelView.ofKernel (linkKernel w.k)
def registeredLink (v : WGKernelView) : WGKernelView :=
  {v with netIfindexNext := v.netIfindexNext + 1, wg := v.wg.map fun d => {d with ifindex := v.netIfindexNext}}

theorem sameLinkView_of_link (ha : SameLinkKernel a) : SameView linkView a := by
  intro w x v hr
  exact congrArg WGKernelView.ofKernel (ha w x v hr)

theorem sameLinkView_of_wg (ha : SameWGKernel a) : SameView linkView a := by
  intro w x v hr
  have he := congrArg (fun k : WGKernelView => {k with wg := k.wg.map linkDevice, ratelimiter := {}}) (ha w x v hr)
  exact he

theorem modifyDev_linkView_spec (P : WGKernelView → Prop) (f : Device → Device)
    (hf : ∀ d, linkDevice (f d) = linkDevice d) :
    ⦃fun w => ⌜P (linkView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (linkView w)⌝⦄ := by
  exact modifyDev_link_spec (fun k => P (WGKernelView.ofKernel k)) f hf

/-- Every normal newlink return is either the early allocation refusal or the
registered endpoint. All other allocation/refusal paths remain original Stops. -/
theorem wgNewlink_endpoint (initial : WGKernelView) :
    ⦃fun w => ⌜linkView w = initial⌝⦄ wgNewlink
    ⦃⇓? ret w => ⌜(ret = -ENOMEM ∧ linkView w = initial) ∨
      (ret = 0 ∧ linkView w = registeredLink initial)⌝⦄ := by
  have hc := (sameLinkView_of_link cookieCheckerInit_sameLinkKernel).wp (fun v => v = initial)
  have hp := (sameLinkView_of_link pubkeyHashtableAlloc_sameLinkKernel).wp (fun v => v = initial)
  have hr := (sameLinkView_of_link (ratelimiter_link ratelimiterInit_sameRatelimiterKernel)).wp (fun v => v = initial)
  have he := fun s => (sameLinkView_of_wg (sameWGKernel_of_sameKernel (envOk_sameKernel s))).wp (fun v => v = initial)
  have hm := (sameLinkView_of_wg (sameWGKernel_of_sameKernel mayHaveSlept_sameKernel)).wp (fun v => v = initial)
  have hs := fun sites => (sameLinkView_of_wg (sameWGKernel_of_sameKernel (skipCut_sameKernel sites))).wp (fun v => v = initial)
  have hx := (sameLinkView_of_wg (KernelFrames.skipCutExactly_sameWGKernel .neighReachTime 2 allocCuts)).wp
    (fun v => v = registeredLink initial)
  have hd := modifyDev_linkView_spec (fun v => v = initial)
  mvcgen [wgNewlink, hc, hp, hr, he, hm, hs, hx, hd, branch, unsupported, getK, modifyK, modifyDev]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [linkView, linkKernel, linkDevice, registeredLink,
    WGKernelView.ofKernel, Option.map_map, Function.comp_def]
  all_goals try assumption
  all_goals try trivial
  all_goals simp_all [WGKernelView.ext_iff, Option.map_map, Function.comp_def, linkDevice]
  rename_i hs hb
  rw [← hs.1]
  simp [Option.map_map, Function.comp_def, linkDevice]


def setupLink (v : WGKernelView) : WGKernelView :=
  {v with wg := some (linkDevice {ifindex := 0, ifname := "wg0", creatingNet := false, deviceUpdateGen := 0})}

/-- The complete guarded create either retains its entry allocation geometry
or installs a fresh empty registered device. No intermediate setup invariant is
claimed, and this normal-endpoint theorem imposes no record-success premise. -/
theorem wgCreate_endpoint (initial : WGKernelView) :
    ⦃fun w => ⌜linkView w = initial⌝⦄ wgCreate
    ⦃⇓? _ w => ⌜linkView w = initial ∨
      (initial.wg = none ∧ linkView w = registeredLink (setupLink initial))⌝⦄ := by
  have hn := wgNewlink_endpoint (setupLink initial)
  mvcgen [wgCreate, wgSetup, hn, getK, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (obtain (⟨rfl, hrun⟩ | ⟨rfl, hrun⟩) := ‹(_ ∧ _) ∨ (_ ∧ _)›)
  all_goals simp_all [linkView, linkKernel, linkDevice, setupLink, registeredLink,
    WGKernelView.ofKernel, WGKernelView.ext_iff, Option.map_map, Function.comp_def, ENOMEM]
  all_goals first | assumption | trivial


end Leanux.Proofs.Framing
