import Leanux.Proofs.WG.Queues.HandshakeLoans
import Leanux.Proofs.WG.Origins.ConfiguredReceive
import Leanux.Proofs.WG.AuthenticatedEffects.RejectedDispatch

/-! Original initiation processing before the first peer lookup. Identity, DH
and static-ciphertext refusals occur entirely in this world-preserving prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
open Leanux.Proofs.WG.Cookies
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def initiationAuthFront (msg : List UInt8) : WG.M (Option (Key × Key × Key × Key)) := do
  let identity := (← getDev).staticIdentity
  if ← branch .consumeNoIdentity !identity.hasIdentity then return none
  let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
  let e := (msg.drop 8).take 32
  let (ck, hash) ← messageEphemeral true e handshakeInitChainingKey hash
  let es ← mixDh true ck identity.staticPrivate e
  if ← branch .consumeEsFailed es.isNone then return none
  let some (ck,key) := es | invariant "unreachable"
  let st ← messageDecrypt ((msg.drop 40).take 48) key hash
  if ← branch .consumeStaticFailed st.isNone then return none
  let some (s,hash) := st | invariant "unreachable"
  return some (e,ck,s,hash)

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl

theorem initiationAuthFront_factor (msg : List UInt8) : consumeInitiation msg = (do
    match ← initiationAuthFront msg with
    | none => initiationOut none none
    | some (e,ck,s,hash) => pubkeyLookup s >>= initiationAfterLookup msg e ck hash) := by
  rw [consumeInitiation_factor]
  unfold initiationAuthFront
  simp only [bind_assoc,if_bind]
  repeat' first
    | with_reducible rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp only [bind_assoc,if_bind,pure_bind,invariant_bind]
  all_goals simp_all only [Option.some.injEq,Prod.mk.injEq]
  all_goals repeat' first
    | with_reducible rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp_all [invariant_bind]

theorem initiationAuthFront_same_world (msg : List UInt8) :
    SameView (id : WGWorld → WGWorld) (initiationAuthFront msg) := by
  intro initial
  change Preserves (fun w : WGWorld => w = initial) _
  unfold initiationAuthFront
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (cookie_source_head invariant; unfold invariant)
    | (cookie_source_head getDev; unfold getDev)
    | (cookie_source_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | receive_crypto (fun w => w = initial)
    | cookie_source_step

theorem initiation_prelookup_refused (msg : List UInt8)
    (w u : WGWorld) (a b : Ambient)
    (front : ((initiationAuthFront msg).run w).run a = .ok ((none,u),b)) :
    ((consumeInitiation msg).run w).run a =
      .ok ((none,w),record (record b .consumeFailedPut true) .peerPutNull true) := by
  have world := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (initiationAuthFront_same_world msg) w a none u b front
  change u = w at world
  rw [initiationAuthFront_factor,Leanux.Proofs.WG.AuthenticatedEffects.native_bind_run,front]
  subst u
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects
