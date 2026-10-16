import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Device

/-! Native lifecycle frames retain the original seven WG observations.
Generic factor laws retain arbitrary additional observations and action stacks. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def ratelimiterStore (v : WGStoreView) : WGStoreView := {v with ratelimiter := {}}
def ratelimiterView (g : WGWorld) : WGStoreView := ratelimiterStore (wgStoreView g)
abbrev SameRatelimiter (a : WG.M α) := SameView ratelimiterView a

theorem mayHaveSlept_sameWGStore : SameWGStore mayHaveSlept := by
  apply SameView.of_wp
  intro initial
  mvcgen [mayHaveSlept]

theorem retireDeviceUnits_sameWGStore : SameWGStore retireDeviceUnits := by
  apply SameView.of_wp
  intro initial
  mvcgen [retireDeviceUnits, modifyAmbient]

theorem ratelimiterInit_sameRatelimiter : SameRatelimiter ratelimiterInit := by
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g : WGWorld => ⌜ratelimiterView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜ratelimiterView g = initial⌝⦄ := hoare_liftAmbient a _
  mvcgen [-Std.Do.Spec.monadLift_StateT, ratelimiterInit, hidden, branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ratelimiterView, ratelimiterStore, wgStoreView]
  all_goals trivial

theorem gcEntries_sameRatelimiter (work : Bool) : SameRatelimiter (gcEntries work) := by
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g : WGWorld => ⌜ratelimiterView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜ratelimiterView g = initial⌝⦄ := hoare_liftAmbient a _
  have hl (α β : Type) := list_view_spec (m := AmbientM) ratelimiterView
    (α := α) (β := β) (fun v => v = initial)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT, hl,
    gcEntries, hiddenClock, branch, unsupported, ha]
  all_goals try exact ((⇓? _ g => ⌜ratelimiterView g = initial⌝) :
    PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ratelimiterView, ratelimiterStore, wgStoreView]
  all_goals trivial

theorem ratelimiterUninit_sameRatelimiter : SameRatelimiter ratelimiterUninit := by
  apply SameView.of_wp
  intro initial
  have hg := fun b => (gcEntries_sameRatelimiter b).wp (fun v => v = initial)
  have hm := (mayHaveSlept_sameWGStore.factor ratelimiterStore).wp (fun v => v = initial)
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g : WGWorld => ⌜ratelimiterView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜ratelimiterView g = initial⌝⦄ := hoare_liftAmbient a _
  mvcgen [-Std.Do.Spec.monadLift_StateT, ratelimiterUninit, hg, hm, skipCut, branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ratelimiterView, ratelimiterStore, wgStoreView]
  all_goals trivial

def linkDevice (d : Device) : Device :=
  {d with creatingNet := false, deviceUpdateGen := 0, cookieSecret := [], cookieSecretBirthdate := 0, pubkeyHashKey := []}
def linkStore (v : WGStoreView) : WGStoreView :=
  {v with ratelimiter := {}, dev := v.dev.map linkDevice}
def linkView (g : WGWorld) : WGStoreView := linkStore (wgStoreView g)
abbrev SameLink (a : WG.M α) := SameView linkView a

/-- Only the WG observation is masked; all additional observations remain
in both the premise and conclusion, for any actual StateT action. -/
theorem ratelimiter_link {S R α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → R × WGStoreView)
    {a : StateT S m α}
    (ha : SameView (fun s => ((project s).1, ratelimiterStore (project s).2)) a) :
    SameView (fun s => ((project s).1, linkStore (project s).2)) a := by
  exact ha.of_factor (fun p : R × WGStoreView => (p.1, linkStore p.2)) _ (fun _ => rfl)

theorem sameLinkView_of_wg {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → WGStoreView)
    {a : StateT S m α} (ha : SameView project a) :
    SameView (fun s => linkStore (project s)) a := ha.factor linkStore

theorem modifyDev_linkView_spec (P : WGStoreView → Prop) (f : Device → Device)
    (hf : ∀ d, linkDevice (f d) = linkDevice d) :
    ⦃fun g => ⌜P (linkView g)⌝⦄ modifyDev f
    ⦃⇓? _ g => ⌜P (linkView g)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient x g' ambient' hp hr
  cases hr
  simpa [linkView, linkStore, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem cookieCheckerInit_sameLink : SameLink cookieCheckerInit := by
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g : WGWorld => ⌜linkView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜linkView g = initial⌝⦄ := hoare_liftAmbient a _
  have hm := modifyDev_linkView_spec (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, cookieCheckerInit, hiddenClock64, hidden, ha, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [linkView, linkStore, wgStoreView, linkDevice, Option.map_map, Function.comp_def]

theorem pubkeyHashtableAlloc_sameLink : SameLink pubkeyHashtableAlloc := by
  apply SameView.of_wp
  intro initial
  have ha (α : Type) (a : AmbientM α) :
      ⦃fun g : WGWorld => ⌜linkView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ g => ⌜linkView g = initial⌝⦄ := hoare_liftAmbient a _
  have hm := modifyDev_linkView_spec (fun s => s = initial)
  mvcgen [-Std.Do.Spec.monadLift_StateT, pubkeyHashtableAlloc, envOk, hidden, ha, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [linkView, linkStore, wgStoreView, linkDevice, Option.map_map, Function.comp_def]

def registeredLink (v : WGStoreView) : WGStoreView :=
  {v with netIfindexNext := v.netIfindexNext + 1, dev := v.dev.map fun d => {d with ifindex := v.netIfindexNext}}

/-- Every normal newlink return is either the early allocation refusal or the
registered endpoint. All other allocation/refusal paths remain original Stops. -/
theorem wgNewlink_endpoint (initial : WGStoreView) :
    ⦃fun g => ⌜linkView g = initial⌝⦄ wgNewlink
    ⦃⇓? ret g => ⌜(ret = -ENOMEM ∧ linkView g = initial) ∨
      (ret = 0 ∧ linkView g = registeredLink initial)⌝⦄ := by
  have hc := cookieCheckerInit_sameLink.wp (fun v => v = initial)
  have hp := pubkeyHashtableAlloc_sameLink.wp (fun v => v = initial)
  have hr : SameLink ratelimiterInit := by
    exact ratelimiterInit_sameRatelimiter.of_factor linkStore linkView (fun _ => rfl)
  have hr := hr.wp (fun v => v = initial)
  have he (s : EnvSite) : ⦃fun g => ⌜linkView g = initial⌝⦄ (envOk s : WG.M Bool)
      ⦃⇓? _ g => ⌜linkView g = initial⌝⦄ := hoare_liftAmbient (AmbientM.envOk s) _
  have hm := (sameLinkView_of_wg wgStoreView mayHaveSlept_sameWGStore).wp (fun v => v = initial)
  have hs (sites : List HiddenSite) : ⦃fun g => ⌜linkView g = initial⌝⦄ (skipCut sites : WG.M Unit)
      ⦃⇓? _ g => ⌜linkView g = initial⌝⦄ := hoare_liftAmbient (AmbientM.skipCut sites) _
  have hx : ⦃fun g => ⌜linkView g = registeredLink initial⌝⦄
      (skipCutExactly .neighReachTime 2 allocCuts : WG.M Unit)
      ⦃⇓? _ g => ⌜linkView g = registeredLink initial⌝⦄ :=
    hoare_liftAmbient (AmbientM.skipCutExactly .neighReachTime 2 allocCuts) _
  have hd := modifyDev_linkView_spec (fun v => v = initial)
  mvcgen [wgNewlink, hc, hp, hr, he, hm, hs, hx, hd, branch, AmbientM.branch,
    unsupported, AmbientM.unsupported, modifyDev]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [linkView, linkStore, linkDevice, registeredLink,
    wgStoreView, Option.map_map, Function.comp_def]
  all_goals try assumption
  all_goals try trivial
  all_goals simp_all [WGStoreView.ext_iff, Option.map_map, Function.comp_def, linkDevice]
  rename_i hs hb
  rw [← hs.1]
  simp [Option.map_map, Function.comp_def, linkDevice]

def setupLink (v : WGStoreView) : WGStoreView :=
  {v with dev := some (linkDevice {ifindex := 0, ifname := "wg0", creatingNet := false, deviceUpdateGen := 0})}

/-- The complete guarded create either retains its entry allocation geometry
or installs a fresh empty registered device, without a record-success premise. -/
theorem wgCreate_endpoint (initial : WGStoreView) :
    ⦃fun g => ⌜linkView g = initial⌝⦄ wgCreate
    ⦃⇓? _ g => ⌜linkView g = initial ∨
      (initial.dev = none ∧ linkView g = registeredLink (setupLink initial))⌝⦄ := by
  have hn := wgNewlink_endpoint (setupLink initial)
  mvcgen [wgCreate, wgSetup, hn]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (obtain (⟨rfl, hrun⟩ | ⟨rfl, hrun⟩) := ‹(_ ∧ _) ∨ (_ ∧ _)›)
  all_goals simp_all [linkView, linkStore, linkDevice, setupLink, registeredLink,
    wgStoreView, WGStoreView.ext_iff, Option.map_map, Function.comp_def, ENOMEM]
  all_goals first | assumption | trivial

end Leanux.Proofs.Framing
