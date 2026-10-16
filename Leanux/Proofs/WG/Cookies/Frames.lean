import Leanux.Proofs.WG.Keypairs.Frames.WGMore
import Leanux.Proofs.Framing.WGTime

/-! The cookie-reply path preserves every device field except its cookie
secret/birthdate and transmit statistics. In particular this includes complete
Noise state, peer/keypair stores, indices and allocation frontiers. -/
namespace Leanux.Proofs.WG.Cookies
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

def scrub (d : Device) : Device :=
  {d with cookieSecret := [], cookieSecretBirthdate := 0, txPackets := 0, txBytes := 0}

def viewOfStore (v : WGStoreView) : Option Device × Nat × Nat :=
  (v.dev.map scrub, v.peerCounter, v.keypairCounter)

def noiseView (w : WGWorld) := viewOfStore (wgStoreView w)

abbrev NoNoiseChange (a : WG.M α) := SameView noiseView a

abbrev FrameSpec (P : (Option Device × Nat × Nat) → Prop) (a : WG.M α) :=
  ⦃fun w => ⌜P (noiseView w)⌝⦄ a ⦃⇓? _ w => ⌜P (noiseView w)⌝⦄

/-- The factor keeps arbitrary actual StateT actions, including product actions. -/
theorem store_frame {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → WGStoreView)
    (a : StateT S m α) (h : SameView project a) :
    SameView (fun s => viewOfStore (project s)) a := h.factor viewOfStore

/-- The generic premise retains the original seven-field store scope. -/
def cookieStore (v : WGStoreView) : WGStoreView :=
  {v with dev := v.dev.map cookieDevice, ratelimiter := {v.ratelimiter with table := [], table6 := []}}

theorem cookie_frame_of_view {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → WGStoreView)
    (a : StateT S m α) (h : SameView (fun s => cookieStore (project s)) a) :
    SameView (fun s => viewOfStore (project s)) a := by
  apply h.of_factor viewOfStore
  intro s
  simp only [cookieStore, viewOfStore, cookieDevice, scrub, Option.map_map, Function.comp_def]
  rfl

theorem modifyDev_spec (P : (Option Device × Nat × Nat) → Prop)
    (f : Device → Device) (hf : ∀ d, scrub (f d) = scrub d) :
    ⦃fun w => ⌜P (noiseView w)⌝⦄ WG.modifyDev f
    ⦃⇓? _ w => ⌜P (noiseView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hp hr
  cases hr
  simpa [noiseView, viewOfStore, wgStoreView, Option.map_map, Function.comp_def, hf] using hp

theorem expired_spec (P : (Option Device × Nat × Nat) → Prop)
    (d : Decision) (b : Int64) (n : Nat) (f : Bool → Bool := id) : FrameSpec P (branchExpired d b n f) :=
  ((branchExpired_sameWGWorld d b n f).factor noiseView).wp P

macro "cookie_frame" "[" fs:ident,* "]" "using" "[" specs:ident,* "]" : tactic => do
  let wrap (term : Lean.Syntax) : Lean.TSyntax [``Lean.Parser.Tactic.simpStar,
      ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] :=
    ⟨Lean.Syntax.node .none ``Lean.Parser.Tactic.simpLemma
      #[Lean.Syntax.missing, Lean.Syntax.missing, term]⟩
  let names := specs.getElems.mapIdx fun i _ => Lean.mkIdent (Lean.Name.mkSimple s!"cookie_spec_{i}")
  let basics := #[``Leanux.WG.getDev, ``Leanux.branch, ``Leanux.AmbientM.branch,
    ``Leanux.AmbientM.branchCmp, ``Leanux.AmbientM.unsupported, ``Leanux.AmbientM.invariant,
    ``Leanux.branchCmp, ``Leanux.unsupported, ``Leanux.invariant,
    ``Leanux.WG.andM, ``Leanux.WG.orM, ``Leanux.getRouting]
  let lemmas := (fs.getElems.map fun f => wrap (if f.getId.toString.startsWith "_private." then
      (Lean.mkCIdent (normalizePinnedName f.getId)).raw else f.raw)) ++
    (basics.map fun n => wrap (Lean.mkIdent n).raw) ++ (names.map fun f => wrap f.raw)
  let mut body ← `(tactic|
    (have hm := modifyDev_spec (fun s => s = initial)
     have ha (site : AllocSite) :
         ⦃fun g => ⌜noiseView g = initial⌝⦄ (hiddenAlloc site : WG.M Bool)
         ⦃⇓? _ g => ⌜noiseView g = initial⌝⦄ := hoare_liftAmbient (AmbientM.hiddenAlloc site) _
     have hc (sites : List HiddenSite) :
         ⦃fun g => ⌜noiseView g = initial⌝⦄ (skipCut sites : WG.M Unit)
         ⦃⇓? _ g => ⌜noiseView g = initial⌝⦄ := hoare_liftAmbient (AmbientM.skipCut sites) _
     have hr (α : Type) (a : Net.M α) :
         ⦃fun g => ⌜noiseView g = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
         ⦃⇓? _ g => ⌜noiseView g = initial⌝⦄ :=
       hoare_liftRouting a _ (fun _ _ hp => hp)
     mvcgen [hm, ha, hc, hr, $lemmas,*]
     all_goals try dsimp +zetaDelta only at *
     all_goals try simp_all [noiseView, viewOfStore, wgStoreView, scrub, Option.map_map, Function.comp_def]
     all_goals try rfl))
  for (name, spec) in (names.zip specs.getElems).reverse do
    body ← `(tactic| (have $name := @$spec (fun s => s = initial); $body))
  `(tactic| (apply SameView.of_wp; intro initial; $body))

theorem makeCookie_frame (src : SkbSource) : NoNoiseChange (makeCookie src) := by
  exact cookie_frame_of_view wgStoreView _ ((makeCookie_sameCookie src).factor WGOwnedView.toWGStoreView)

theorem makeCookie_spec (P : (Option Device × Nat × Nat) → Prop) (src : SkbSource) : FrameSpec P (makeCookie src) :=
  (makeCookie_frame src).wp P

theorem socketPort_frame (family : Nat) : NoNoiseChange (socketPort family) := by
  cookie_frame [socketPort] using []
theorem socketPort_spec (P : (Option Device × Nat × Nat) → Prop) (family : Nat) : FrameSpec P (socketPort family) :=
  (socketPort_frame family).wp P

theorem tunnel_frame (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) :
    NoNoiseChange ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit)
      e bytes ds r false) := by
  cookie_frame [_private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit]
    using [socketPort_spec]
theorem tunnel_spec (P : (Option Device × Nat × Nat) → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) : FrameSpec P ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r false) :=
  (tunnel_frame e bytes ds r).wp P

theorem send4_reply_frame (e : Endpoint) (bytes : List UInt8) (ds : Nat) :
    NoNoiseChange (send4 e none bytes ds false) := by
  cookie_frame [send4] using [tunnel_spec]
theorem send4_reply_spec (P : (Option Device × Nat × Nat) → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) : FrameSpec P (send4 e none bytes ds false) :=
  (send4_reply_frame e bytes ds).wp P

theorem send6_reply_frame (e : Endpoint) (bytes : List UInt8) (ds : Nat) :
    NoNoiseChange (send6 e none bytes ds false) := by
  cookie_frame [send6] using [tunnel_spec]
theorem send6_reply_spec (P : (Option Device × Nat × Nat) → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) : FrameSpec P (send6 e none bytes ds false) :=
  (send6_reply_frame e bytes ds).wp P

theorem sendBufferReply_frame (src : SkbSource) (bytes : List UInt8) :
    NoNoiseChange (sendBufferAsReplyToSkb src bytes) := by
  cookie_frame [sendBufferAsReplyToSkb, endpointFromSkb]
    using [send4_reply_spec, send6_reply_spec]
theorem sendBufferReply_spec (P : (Option Device × Nat × Nat) → Prop)
    (src : SkbSource) (bytes : List UInt8) : FrameSpec P (sendBufferAsReplyToSkb src bytes) :=
  (sendBufferReply_frame src bytes).wp P

theorem cookieMessageCreate_frame (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    NoNoiseChange (cookieMessageCreate index src mac1) := by
  exact cookie_frame_of_view wgStoreView _ ((cookieMessageCreate_sameCookie index src mac1).factor WGOwnedView.toWGStoreView)
theorem cookieMessageCreate_spec (P : (Option Device × Nat × Nat) → Prop)
    (index : Nat) (src : SkbSource) (mac1 : List UInt8) : FrameSpec P (cookieMessageCreate index src mac1) :=
  (cookieMessageCreate_frame index src mac1).wp P

theorem sendHandshakeCookie_frame (msg : List UInt8) (src : SkbSource) :
    NoNoiseChange (sendHandshakeCookie msg src) := by
  cookie_frame [sendHandshakeCookie] using [cookieMessageCreate_spec, sendBufferReply_spec]

end Leanux.Proofs.WG.Cookies
