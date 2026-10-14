import Leanux.Proofs.WG.Keypairs.Frames.WGMore
import Leanux.Proofs.Framing.WGTime

/-! The cookie-reply path preserves every device field except its cookie
secret/birthdate and transmit statistics. In particular this includes complete
Noise state, peer/keypair stores, indices and allocation frontiers. -/
namespace Leanux.Proofs.WG.Cookies
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

def scrub (d : Device) : Device :=
  {d with cookieSecret := [], cookieSecretBirthdate := 0, txPackets := 0, txBytes := 0}

def viewOfKernel (k : Kernel) : Option Device × Nat × Nat :=
  (k.wg.map scrub, k.peerCounter, k.keypairCounter)

def noiseView (w : World) := viewOfKernel w.k

abbrev NoNoiseChange (a : M α) := SameView noiseView a

abbrev FrameSpec (P : (Option Device × Nat × Nat) → Prop) (a : M α) :=
  ⦃fun w => ⌜P (noiseView w)⌝⦄ a ⦃⇓? _ w => ⌜P (noiseView w)⌝⦄

theorem kernel_frame (a : M α) (h : SameKernel a) : NoNoiseChange a :=
  SameView.of_sameKernel viewOfKernel h

theorem cookieKernel_frame (a : M α) (h : SameCookieKernel a) : NoNoiseChange a := by
  intro w x v hr
  have hf := congrArg viewOfKernel (h w x v hr)
  have he (k : Kernel) : viewOfKernel (cookieKernel k) = viewOfKernel k := by
    unfold viewOfKernel cookieKernel
    simp only [Option.map_map]
    rfl
  simpa only [cookieKernelView, noiseView, he] using hf

theorem modifyDev_spec (P : (Option Device × Nat × Nat) → Prop)
    (f : Device → Device) (hf : ∀ d, scrub (f d) = scrub d) :
    ⦃fun w => ⌜P (noiseView w)⌝⦄ WG.modifyDev f
    ⦃⇓? _ w => ⌜P (noiseView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [noiseView, viewOfKernel, Option.map_map, Function.comp_def, hf] using hp

theorem hidden_spec (P : (Option Device × Nat × Nat) → Prop) (s : HiddenSite) : FrameSpec P (hidden s) :=
  (kernel_frame _ (hidden_sameKernel s)).wp P
theorem clock_spec (P : (Option Device × Nat × Nat) → Prop) (s : HiddenSite) : FrameSpec P (hiddenClock64 s) :=
  (kernel_frame _ (hiddenClock64_sameKernel s)).wp P
theorem expired_spec (P : (Option Device × Nat × Nat) → Prop)
    (d : Decision) (b : Int64) (n : Nat) (f : Bool → Bool := id) : FrameSpec P (branchExpired d b n f) :=
  (kernel_frame _ (branchExpired_sameKernel d b n f)).wp P
theorem alloc_spec (P : (Option Device × Nat × Nat) → Prop) (s : AllocSite) : FrameSpec P (hiddenAlloc s) :=
  (kernel_frame _ (hiddenAlloc_sameKernel s)).wp P
theorem route_spec (P : (Option Device × Nat × Nat) → Prop) (f s d : Nat) : FrameSpec P (routeLookup f s d) :=
  (kernel_frame _ (routeLookup_sameKernel f s d)).wp P
theorem cut_spec (P : (Option Device × Nat × Nat) → Prop) (ss : List HiddenSite) : FrameSpec P (skipCut ss) :=
  (kernel_frame _ (skipCut_sameKernel ss)).wp P

macro "cookie_frame" "[" fs:ident,* "]" "using" "[" specs:ident,* "]" : tactic => do
  let wrap (term : Lean.Syntax) : Lean.TSyntax [``Lean.Parser.Tactic.simpStar,
      ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] :=
    ⟨Lean.Syntax.node .none ``Lean.Parser.Tactic.simpLemma
      #[Lean.Syntax.missing, Lean.Syntax.missing, term]⟩
  let names := specs.getElems.mapIdx fun i _ => Lean.mkIdent (Lean.Name.mkSimple s!"cookie_spec_{i}")
  let basics := #[``Leanux.getK, ``Leanux.WG.getDev, ``Leanux.branch,
    ``Leanux.branchCmp, ``Leanux.unsupported, ``Leanux.invariant,
    ``Leanux.WG.andM, ``Leanux.WG.orM]
  let lemmas := (fs.getElems.map fun f => wrap (if f.getId.toString.startsWith "_private." then
      (Lean.mkCIdent (normalizePinnedName f.getId)).raw else f.raw)) ++
    (basics.map fun n => wrap (Lean.mkIdent n).raw) ++ (names.map fun f => wrap f.raw)
  let mut body ← `(tactic|
    (have hm := modifyDev_spec (fun s => s = initial)
     mvcgen [hm, $lemmas,*]
     all_goals try dsimp +zetaDelta only at *
     all_goals try simp_all [noiseView, viewOfKernel, scrub, Option.map_map, Function.comp_def]
     all_goals try rfl))
  for (name, spec) in (names.zip specs.getElems).reverse do
    body ← `(tactic| (have $name := @$spec (fun s => s = initial); $body))
  `(tactic| (apply SameView.of_wp; intro initial; $body))

theorem makeCookie_frame (src : SkbSource) : NoNoiseChange (makeCookie src) := by
  exact cookieKernel_frame _ (makeCookie_sameCookieKernel src)

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
    using [cut_spec, socketPort_spec]
theorem tunnel_spec (P : (Option Device × Nat × Nat) → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) : FrameSpec P ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r false) :=
  (tunnel_frame e bytes ds r).wp P

theorem send4_reply_frame (e : Endpoint) (bytes : List UInt8) (ds : Nat) :
    NoNoiseChange (send4 e none bytes ds false) := by
  cookie_frame [send4] using [route_spec, tunnel_spec]
theorem send4_reply_spec (P : (Option Device × Nat × Nat) → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) : FrameSpec P (send4 e none bytes ds false) :=
  (send4_reply_frame e bytes ds).wp P

theorem send6_reply_frame (e : Endpoint) (bytes : List UInt8) (ds : Nat) :
    NoNoiseChange (send6 e none bytes ds false) := by
  cookie_frame [send6] using [route_spec, tunnel_spec]
theorem send6_reply_spec (P : (Option Device × Nat × Nat) → Prop)
    (e : Endpoint) (bytes : List UInt8) (ds : Nat) : FrameSpec P (send6 e none bytes ds false) :=
  (send6_reply_frame e bytes ds).wp P

theorem sendBufferReply_frame (src : SkbSource) (bytes : List UInt8) :
    NoNoiseChange (sendBufferAsReplyToSkb src bytes) := by
  cookie_frame [sendBufferAsReplyToSkb, endpointFromSkb]
    using [alloc_spec, send4_reply_spec, send6_reply_spec]
theorem sendBufferReply_spec (P : (Option Device × Nat × Nat) → Prop)
    (src : SkbSource) (bytes : List UInt8) : FrameSpec P (sendBufferAsReplyToSkb src bytes) :=
  (sendBufferReply_frame src bytes).wp P

theorem cookieMessageCreate_frame (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    NoNoiseChange (cookieMessageCreate index src mac1) := by
  exact cookieKernel_frame _ (cookieMessageCreate_sameCookieKernel index src mac1)
theorem cookieMessageCreate_spec (P : (Option Device × Nat × Nat) → Prop)
    (index : Nat) (src : SkbSource) (mac1 : List UInt8) : FrameSpec P (cookieMessageCreate index src mac1) :=
  (cookieMessageCreate_frame index src mac1).wp P

theorem sendHandshakeCookie_frame (msg : List UInt8) (src : SkbSource) :
    NoNoiseChange (sendHandshakeCookie msg src) := by
  cookie_frame [sendHandshakeCookie] using [cookieMessageCreate_spec, sendBufferReply_spec]

end Leanux.Proofs.WG.Cookies
