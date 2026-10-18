import Leanux.Proofs.WG.AuthenticatedEffects.ReplySource
import Leanux.Proofs.WG.AuthenticatedEffects.TunnelSource
import Leanux.Proofs.WG.AuthenticatedEffects.Socket4Source
import Leanux.Proofs.WG.AuthenticatedEffects.Socket6Source

/-! Frames for the egress queue, separate from the native source factors. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Cookies Std.Do

macro "sent_frame" "[" fs:ident,* "]" "using" "[" specs:ident,* "]" : tactic => do
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
      ``Leanux.invariant, ``Leanux.hiddenAlloc, ``Leanux.hidden, ``Leanux.hiddenClock64, ``Leanux.skipCut,
      ``Leanux.WG.andM, ``Leanux.WG.orM, ``Leanux.getRouting, ``liftM].reverse do
    let n := Lean.mkCIdent name
    atom ← `(tactic| first | (cookie_source_head $n; unfold $n) | ($atom:tactic))
  let mut body ← `(tactic|
    (let P := fun w : WGWorld => w.sent = initial
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
     have write (f : Device → Device) : Preserves P (WG.modifyDev f) := by
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a x v b hi hr
       cases hr
       exact hi
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
       | (cookie_source_head WG.modifyDev; exact write _)
       | (cookie_source_head modify; apply hoare_modify; intro w hi; exact hi)
       | (cookie_source_lift AmbientM; exact ambient _)
       | (cookie_source_lift Net.M; exact routing _)
       | (cookie_source_head liftRouting; exact routing _)
       | cookie_source_step))
  for (name, spec) in (names.zip specs.getElems).reverse do
    body ← `(tactic| (have $name := @$spec (fun s => s = initial); $body))
  `(tactic| (intro initial; $body))

theorem replyFront_sent (src : SkbSource) : SameView WGWorld.sent (replyFront src) := by
  sent_frame [replyFront, endpointFromSkb] using []
theorem socketPort_sent (family : Nat) : SameView WGWorld.sent (socketPort family) := by
  sent_frame [socketPort] using []

theorem socketPort_sent_spec (P : List SentDatagram → Prop) (family : Nat) :
    Preserves (fun w => P w.sent) (socketPort family) := (socketPort_sent family).wp P

theorem tunnelReplyFront_sent (e : Endpoint) (bytes : List UInt8) (r : Route) :
    SameView WGWorld.sent (tunnelReplyFront e bytes r) := by
  sent_frame [tunnelReplyFront] using [socketPort_sent_spec]

theorem socket4Front_sent (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView WGWorld.sent (socket4Front e none bytes ds exactRx) := by
  sent_frame [socket4Front, socket4AfterCacheFront, socket4MissFront, socket4RetryFront,
    socket4RouteFront, socket4FinishFront, Leanux.Proofs.WG.Lifetimes.send4ClearSrcSource] using []

theorem socket6Front_sent (e : Endpoint) : SameView WGWorld.sent (socket6Front e none) := by
  sent_frame [socket6Front] using []

theorem expired_sent_spec (P : List SentDatagram → Prop) (d : Decision)
    (birth : Int64) (seconds : Nat) (f : Bool → Bool := id) :
    Preserves (fun w => P w.sent) (branchExpired d birth seconds f) :=
  ((branchExpired_sameWGWorld d birth seconds f).factor WGWorld.sent).wp P

theorem makeCookie_sent (src : SkbSource) : SameView WGWorld.sent (makeCookie src) := by
  sent_frame [makeCookie] using [expired_sent_spec]

theorem makeCookie_sent_spec (P : List SentDatagram → Prop) (src : SkbSource) :
    Preserves (fun w => P w.sent) (makeCookie src) := (makeCookie_sent src).wp P

theorem cookieMessageCreate_sent (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    SameView WGWorld.sent (cookieMessageCreate index src mac1) := by
  sent_frame [cookieMessageCreate] using [makeCookie_sent_spec]

theorem loadPhase_sent : SameView WGWorld.sent loadPhase := by
  sent_frame [loadPhase, birthdateTest] using []

end Leanux.Proofs.WG.AuthenticatedEffects
