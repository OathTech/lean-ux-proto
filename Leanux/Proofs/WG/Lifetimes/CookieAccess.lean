import Lean
import Leanux.Proofs.WG.Lifetimes.LookupAccess
import Leanux.Proofs.Framing.WGCookie

/-! Complete local cookie calls. Make/create/validate inspect device and
ratelimiter data but no resident peer, keypair or packet. Consumption observes
the reference-taking lookup, peer reads/writes and each original final put.
Record failures retain the prefix and do not execute later cleanup. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

-- Introduce callback binders without unfolding execution contracts.
elab "cookie_intro_forall" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected an explicit function argument"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro x))

/-- The original seven WG store fields with only cookie secrets and limiter
tables masked. The newer routing/timer observations are outside this premise. -/
def cookieStoreView (w : WGWorld) : WGStoreView := (cookieView w).toWGStoreView

/-- The omitted fields affect neither logical residents nor allocator geometry. -/
theorem cookieKernel_identity_metadata (w v : WGWorld)
    (he : cookieStoreView v = cookieStoreView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun k : WGStoreView => identityView {w with dev := k.dev, peerCounter := k.peerCounter}) he
  have hm := congrArg (fun k : WGStoreView => allocationMetadata {w with dev := k.dev, keypairCounter := k.keypairCounter, netIfindexNext := k.netIfindexNext}) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [cookieStoreView, cookieView, wgOwnedView, wgStoreView, cookieDevice, Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [cookieStoreView, cookieView, wgOwnedView, wgStoreView, cookieDevice, Option.map_map, Function.comp_def] using hm

/-- An arbitrary ambient invariant must explicitly permit these cookie-state
updates; unchanged resident identities alone would not suffice for it. -/
def CookieStable (I : List LifetimeEvent → WGWorld → Prop) : Prop :=
  ∀ h w v, cookieStoreView v = cookieStoreView w → I h w → I h v

theorem allocationCookieStable : CookieStable AllocationInv := by
  intro h w v he hi
  have hf := cookieKernel_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem cookieLift_spec (c : AmbientContracts I) (hc : CookieStable I)
    (P : IdentityView → Prop) (a : WG.M α) (ha : SameView cookieStoreView a) :
    AmbientSpec I P (liftWGPrefix a) (fun _ => P) := by
  apply StatePrefixEnsures.lift a (fun h w _ hi => c.safe h w hi.1)
  intro h w ambient x v ambient' hi hr
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v = identityView w :=
    congrArg Prod.fst (cookieKernel_identity_metadata w v hf)
  change P (identityView v)
  rw [hid]
  exact hi.2

/-- The original 43-field product observation remains available for arbitrary
product actions and invariants, with exactly the cookie-state mask. -/
def productCookieView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter), cookieStoreView w.wg)

def ProductCookieStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, productCookieView v = productCookieView w → I h w → I h v

theorem cookieLift_spec_product (c : ProductAmbientContracts I) (hc : ProductCookieStable I)
    (P : IdentityView → Prop) (a : Leanux.M α) (ha : SameView productCookieView a) :
    ProductAmbientSpec I P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun h w hi => c.safe h w hi.1)
  intro h w x v hi hr
  have hf := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hcookie : cookieStoreView v.wg = cookieStoreView w.wg :=
    congrArg (fun s : ProductStore43 => s.2.2.2) hf
  have hid : identityView v.wg = identityView w.wg :=
    congrArg Prod.fst (cookieKernel_identity_metadata w.wg v.wg hcookie)
  change P (identityView v.wg)
  rw [hid]
  exact hi.2

def cookieMessageConsumePrefix (msg : List UInt8) : MixedM Unit := do
  let entry ← indexLookupPrefix [.handshake, .keypair] (u32le msg 4)
  if ← liftWGPrefix (branch .cookieLookupMiss entry.isNone) then return
  let some (_, pid) := entry | liftWGPrefix (invariant "unreachable")
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branch .cookieNoMac1Sent !p.haveSentMac1) then
    peerPutMixed (some pid)
    return
  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent
  if ← liftWGPrefix (branch .cookieDecryptOk cookie.isSome) then
    let some value := cookie | liftWGPrefix (invariant "unreachable")
    let birthdate ← liftWGPrefix (hiddenClock64 .cookieBirthdate)
    modifyPeerKeysPrefix pid fun p => {p with
      cookie := value
      cookieBirthdate := birthdate
      cookieIsValid := true
      haveSentMac1 := false}
  peerPutMixed (some pid)

theorem cookieMessageConsumePrefix_erases (msg : List UInt8) :
    ErasesStatePrefix (cookieMessageConsumePrefix msg) (cookieMessageConsume msg) := by
  unfold cookieMessageConsumePrefix cookieMessageConsume modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact indexLookupPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply erasesStatePrefix_ite
    | (cookie_intro_forall; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals first | exact setPeerMixed_erases _ _ | exact erasesStatePrefix_lift _ | exact erasesStatePrefix_pure _

theorem cookieMessageConsumePrefix_preserves (c : AmbientContracts I) (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (cookieMessageConsumePrefix msg) := by
  have clock_spec :
      AmbientSpec I (fun _ => True) (liftWGPrefix (hiddenClock64 .cookieBirthdate)) (fun _ _ => True) := by
    apply c.store
    intro initial
    exact hoare_liftAmbient (AmbientM.hiddenClock64 .cookieBirthdate) (fun w => wgStoreView w = initial)
  unfold cookieMessageConsumePrefix
  repeat' first
    | with_reducible exact indexLookupPrefix_preserves_ambient c _ _
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop clock_spec
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.pure (fun _ => True) _)
    | with_reducible apply StatePrefixEnsures.bind
    | with_reducible apply StatePrefixEnsures.ite
    | (cookie_intro_forall; try dsimp only)
    | (with_reducible split)

/-- The caller invariant still ranges over the complete actual product. -/
theorem cookieMessageConsumePrefix_preserves_product (c : ProductAmbientContracts I)
    (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (cookieMessageConsumePrefix msg)) := by
  have clock_spec : ProductAmbientSpec I (fun _ => True)
      (liftWGObserver (liftWGPrefix (hiddenClock64 .cookieBirthdate))) (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.hiddenClock64 .cookieBirthdate) (fun w => wgStoreView w = initial)
  have branch_spec (d : Decision) (b : Bool) : ProductAmbientSpec I (fun _ => True)
      (liftWGObserver (liftWGPrefix (branch d b))) (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (why : String) : ProductAmbientSpec I (fun _ => True)
      (liftWGObserver (liftWGPrefix (invariant (α := Unit) why))) (fun _ _ => True) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  unfold cookieMessageConsumePrefix
  simp only [liftWGObserver_bind]
  repeat' first
    | with_reducible exact indexLookupPrefix_preserves_product c _ _
    | with_reducible exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact c.peerPut _
    | with_reducible exact ProductAmbientContracts.drop clock_spec
    | with_reducible exact ProductAmbientContracts.drop (branch_spec _ _)
    | with_reducible exact ProductAmbientContracts.drop (invariant_spec _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (cookie_intro_forall; try dsimp only)
    | (with_reducible split)
    | simp only [liftWGObserver_bind, liftWGObserver_pure]

inductive CookieCall where
  | make (src : SkbSource)
  | create (index : Nat) (src : SkbSource) (mac1 : List UInt8)
  | validate (msg : List UInt8) (src : SkbSource) (checkCookie : Bool)
  | consume (msg : List UInt8)

namespace CookieCall

def Result : CookieCall → Type
  | .make .. | .create .. => List UInt8
  | .validate .. => MacState
  | .consume .. => Unit

def original (call : CookieCall) : WG.M call.Result := match call with
  | .make src => makeCookie src
  | .create index src mac1 => cookieMessageCreate index src mac1
  | .validate msg src checkCookie => cookieValidatePacket msg src checkCookie
  | .consume msg => cookieMessageConsume msg

def observed (call : CookieCall) : MixedM call.Result := match call with
  | .make src => liftWGPrefix (makeCookie src)
  | .create index src mac1 => liftWGPrefix (cookieMessageCreate index src mac1)
  | .validate msg src checkCookie => liftWGPrefix (cookieValidatePacket msg src checkCookie)
  | .consume msg => cookieMessageConsumePrefix msg

theorem erases (call : CookieCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | make src => exact erasesStatePrefix_lift _
  | create index src mac1 => exact erasesStatePrefix_lift _
  | validate msg src checkCookie => exact erasesStatePrefix_lift _
  | consume msg => exact cookieMessageConsumePrefix_erases msg

theorem preserves_ambient (c : AmbientContracts I) (hc : CookieStable I)
    (call : CookieCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | make src => exact AmbientContracts.drop (cookieLift_spec c hc (fun _ => True) _ ((makeCookie_sameCookie src).factor WGOwnedView.toWGStoreView))
  | create index src mac1 => exact AmbientContracts.drop (cookieLift_spec c hc (fun _ => True) _ ((cookieMessageCreate_sameCookie index src mac1).factor WGOwnedView.toWGStoreView))
  | validate msg src checkCookie => exact AmbientContracts.drop (cookieLift_spec c hc (fun _ => True) _ ((cookieValidatePacket_sameCookie msg src checkCookie).factor WGOwnedView.toWGStoreView))
  | consume msg => exact cookieMessageConsumePrefix_preserves c msg

theorem preserves_product (c : ProductAmbientContracts I) (hc : ProductCookieStable I)
    (call : CookieCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  have lift_spec (α : Type) (a : WG.M α) (ha : SameCookie a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) := by
    rw [liftWGObserver_lift]
    apply ProductAmbientContracts.drop (cookieLift_spec_product c hc (fun _ => True) (liftWG a) ?_)
    apply sameView_liftWG productCookieView cookieStoreView a (ha.factor WGOwnedView.toWGStoreView)
    intro w g ambient hg
    simp only [productCookieView, hg]
  cases call with
  | make src => exact lift_spec _ _ (makeCookie_sameCookie src)
  | create index src mac1 => exact lift_spec _ _ (cookieMessageCreate_sameCookie index src mac1)
  | validate msg src checkCookie => exact lift_spec _ _ (cookieValidatePacket_sameCookie msg src checkCookie)
  | consume msg => exact cookieMessageConsumePrefix_preserves_product c msg

theorem allocation (call : CookieCall) : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationCookieStable

end CookieCall
end Leanux.Proofs.WG.Lifetimes
