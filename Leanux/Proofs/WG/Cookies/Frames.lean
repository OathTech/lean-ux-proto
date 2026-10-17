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

open Lean Meta Elab Tactic in
elab "cookie_source_head " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a frame contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo n
  unless action.getAppFn.constName? == some expected do throwError "different action head"

open Lean Meta Elab Tactic in
elab "cookie_source_lift " carrier:ident : tactic => withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.isAppOf ``Preserves do
    throwError "expected a frame contract"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.isAppOf ``liftM || action.isAppOf ``MonadLift.monadLift ||
      action.isAppOf ``MonadLiftT.monadLift do
    throwError "expected a lifted action"
  let source := action.getAppArgs.back!
  let sourceType ← inferType source
  unless sourceType.isApp do throwError "expected an applied source monad"
  let name ← realizeGlobalConstNoOverloadWithInfo carrier
  let expected ← mkAppM name #[sourceType.getAppArgs.back!]
  unless ← withReducible (isDefEq sourceType expected) do
    throwError "different source monad"
open Lean Meta Elab Tactic in
elab "cookie_source_fact " n:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let .app _ action := target | throwError "missing cookie action"
  let proof ← Lean.Elab.Term.elabTerm n none
  let (_, _, conclusion) ← forallMetaTelescope (← instantiateMVars (← inferType proof))
  let conclusion := (← instantiateMVars conclusion).consumeMData
  let args := conclusion.getAppArgs
  let framed ← if conclusion.isAppOf ``Std.Do.Triple || conclusion.isAppOf ``Hoare then do
      unless args.size ≥ 3 do throwError "incomplete cookie contract"
      pure args[args.size - 3]!
    else do
      unless args.size > 0 do throwError "missing named action"
      pure args.back!
  let actualHead := action.consumeMData.headBeta.getAppFn
  let framedHead := framed.consumeMData.headBeta.getAppFn
  let sameHead := match actualHead.constName?, framedHead.constName? with
    | some actual, some expected =>
      actual == expected ||
        ((actual == ``MonadLift.monadLift || actual == ``MonadLiftT.monadLift) &&
          (expected == ``MonadLift.monadLift || expected == ``MonadLiftT.monadLift))
    | _, _ => actualHead == framedHead
  unless sameHead do throwError "different cookie action"
  replaceMainGoal (← goal.apply proof)

open Lean Meta Elab Tactic in
elab "cookie_source_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  if target.isForall then
    evalTactic (← `(tactic| intro))
    return
  unless target.isAppOf ``Preserves do throwError "expected a cookie preservation contract"
  let .app property action := target | throwError "missing cookie action"
  let action := action.consumeMData
  if let .letE name ty value body _ := action then
    if name.toString.startsWith "__do_jp" || name.eraseMacroScopes == `err then
      let claim ← forallTelescope ty fun args _ =>
        mkForallFVars args (mkApp property (mkAppN value args))
      let proof ← mkFreshExprSyntheticOpaqueMVar claim
      let (continuation, next) ← withLocalDeclD name ty fun f => do
        let claim ← forallTelescope ty fun args _ =>
          mkForallFVars args (mkApp property (mkAppN f args))
        withLocalDeclD `cookie_join claim fun hf => do
          let next ← mkFreshExprSyntheticOpaqueMVar (mkApp property (body.instantiate1 f))
          return (← mkLambdaFVars #[f, hf] next, next.mvarId!)
      goal.assign (mkApp2 continuation value proof)
      replaceMainGoal [proof.mvarId!, next]
    else
      replaceMainGoal [← goal.replaceTargetDefEq (mkApp property (body.instantiate1 value))]
    return
  if let .letE _ _ value body _ := action.getAppFn.consumeMData then
    replaceMainGoal [← goal.replaceTargetDefEq
      (mkApp property (mkAppN (body.instantiate1 value) action.getAppArgs))]
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replaceMainGoal [← goal.replaceTargetDefEq (mkApp property reduced)]
    return
  if action.getAppFn.isFVar then
    for decl in ← getLCtx do
      if decl.userName == `cookie_join then
        let proof := mkAppN decl.toExpr action.getAppArgs
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
    throwError "missing cookie continuation contract"
  let head := action.getAppFn.constName?
  if head == some ``Bind.bind then
    evalTactic (← `(tactic| refine preserves_bind ?_ ?_))
  else if head == some ``Pure.pure then
    evalTactic (← `(tactic| exact preserves_pure _))
  else if head == some ``ite || head == some ``dite then
    evalTactic (← `(tactic| split))
  else if head == some ``liftM then
    evalTactic (← `(tactic| unfold liftM))
  else if (← Lean.Meta.matchMatcherApp? action).isSome then
    replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)
  else
    throwError "unhandled cookie action head {head}"

macro "cookie_frame" "[" fs:ident,* "]" "using" "[" specs:ident,* "]" : tactic => do
  let pinned := fs.getElems.map fun f =>
    if f.getId.toString.startsWith "_private." then
      Lean.mkCIdent (normalizePinnedName f.getId) else f
  let names := specs.getElems.mapIdx fun i _ => Lean.mkIdent (Lean.Name.mkSimple s!"cookie_spec_{i}")
  let mut use ← `(tactic| fail "no named cookie source fact")
  for name in names.reverse do
    use ← `(tactic| first | cookie_source_fact $name | ($use:tactic))
  let expand ← if pinned.isEmpty then `(tactic| skip) else `(tactic| unfold $pinned:ident*)
  let mut atom ← `(tactic| fail "not a cookie source wrapper")
  for name in #[``Leanux.branch, ``Leanux.branchCmp, ``Leanux.unsupported,
      ``Leanux.invariant, ``Leanux.hiddenAlloc, ``Leanux.skipCut,
      ``Leanux.WG.andM, ``Leanux.WG.orM, ``Leanux.getRouting, ``liftM].reverse do
    let n := Lean.mkCIdent name
    atom ← `(tactic| first | (cookie_source_head $n; unfold $n) | ($atom:tactic))
  let mut body ← `(tactic|
    (let P := fun w : WGWorld => noiseView w = initial
     change Preserves P _
     have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
       hoare_liftAmbient a P
     have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) :=
       hoare_liftRouting a P (fun _ _ hp => hp)
     have device : Preserves P getDev := by
       unfold getDev
       apply preserves_bind (hoare_consequence (hoare_get P)
         (fun _ h => h) (fun _ _ h => h.2))
       intro w
       cases w.dev
       · exact ambient (AmbientM.invariant "no WireGuard device in this trace's fixture")
       · exact preserves_pure _
     have read : Preserves P (get : WG.M WGWorld) :=
       hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
     have write (f : Device → Device) (hf : ∀ d, scrub (f d) = scrub d) :
         Preserves P (WG.modifyDev f) := modifyDev_spec (fun s => s = initial) f hf
     have sourceBranch {β : Type} (d : Decision) (b : Bool) (f : Bool → WG.M β)
         (hf : Preserves P (f b)) : Preserves P ((branch d b : WG.M Bool) >>= f) := by
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a x out a' hi hr
       change ((f b).run w).run _ = .ok ((x, out), a') at hr
       exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
     $expand
     repeat' first
       | contradiction
       | (run_tac Lean.Elab.Tactic.withMainContext do
            let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
            unless target.isAppOf ``Preserves do throwError "not a cookie frame"
            let .app _ action := target | throwError "missing action"
            unless action.isAppOf ``Bind.bind do throwError "not a bind"
            let args := action.getAppArgs
            unless args.size ≥ 2 do throwError "incomplete bind"
            unless args[args.size - 2]!.consumeMData.isAppOf ``Leanux.branch do
              throwError "not a recorded branch"
          apply sourceBranch)
       | ($use:tactic)
       | ($atom:tactic)
       | (cookie_source_head getDev; exact device)
       | (cookie_source_head get; exact read)
       | (cookie_source_head MonadStateOf.get; exact read)
       | (cookie_source_head WG.modifyDev; exact write _ (fun _ => rfl))
       | (cookie_source_head modify; apply hoare_modify; intro w hi; exact hi)
       | (cookie_source_lift AmbientM; exact ambient _)
       | (cookie_source_lift Net.M; exact routing _)
       | cookie_source_step))
  for (name, spec) in (names.zip specs.getElems).reverse do
    body ← `(tactic| (have $name := @$spec (fun s => s = initial); $body))
  `(tactic| (intro initial; $body))

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
