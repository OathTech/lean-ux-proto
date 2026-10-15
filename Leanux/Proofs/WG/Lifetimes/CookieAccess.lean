import Leanux.Proofs.WG.Lifetimes.LookupAccess
import Leanux.Proofs.Framing.WGCookie

/-! Complete local cookie calls. Make/create/validate inspect device and
ratelimiter data but no resident peer, keypair or packet. Consumption observes
the reference-taking lookup, peer reads/writes and each original final put.
Record failures retain the prefix and do not execute later cleanup. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- The omitted fields affect neither logical residents nor allocator geometry. -/
theorem cookieKernel_identity_metadata (w v : World)
    (he : cookieKernelView v = cookieKernelView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun k => identityView {w with k}) he
  have hm := congrArg (fun k => allocationMetadata {w with k}) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [cookieKernelView, cookieKernel, cookieDevice, Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [cookieKernelView, cookieKernel, cookieDevice, Option.map_map, Function.comp_def] using hm

/-- An arbitrary ambient invariant must explicitly permit these cookie-state
updates; unchanged resident identities alone would not suffice for it. -/
def CookieStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, cookieKernelView v = cookieKernelView w → I h w → I h v

theorem allocationCookieStable : CookieStable AllocationInv := by
  intro h w v he hi
  have hf := cookieKernel_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem cookieLift_spec (c : AmbientContracts I) (hc : CookieStable I)
    (P : IdentityView → Prop) (a : M α) (ha : SameCookieKernel a) :
    AmbientSpec I P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun _ _ hi => c.safe _ _ hi.1)
  intro h w x v hi hr
  have hf := ha w x v hr
  refine ⟨hc h w v hf hi.1, ?_⟩
  have hid : identityView v = identityView w :=
    congrArg Prod.fst (cookieKernel_identity_metadata w v hf)
  change P (identityView v)
  rw [hid]
  exact hi.2

def cookieMessageConsumePrefix (msg : List UInt8) : MixedM Unit := do
  let entry ← indexLookupPrefix [.handshake, .keypair] (u32le msg 4)
  if ← liftPrefix (branch .cookieLookupMiss entry.isNone) then return
  let some (_, pid) := entry | liftPrefix (invariant "unreachable")
  let p ← getPeerMixed pid
  if ← liftPrefix (branch .cookieNoMac1Sent !p.haveSentMac1) then
    peerPutMixed (some pid)
    return
  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent
  if ← liftPrefix (branch .cookieDecryptOk cookie.isSome) then
    let some value := cookie | liftPrefix (invariant "unreachable")
    let birthdate ← liftPrefix (hiddenClock64 .cookieBirthdate)
    modifyPeerKeysPrefix pid fun p => {p with
      cookie := value
      cookieBirthdate := birthdate
      cookieIsValid := true
      haveSentMac1 := false}
  peerPutMixed (some pid)

theorem cookieMessageConsumePrefix_erases (msg : List UInt8) :
    ErasesPrefix (cookieMessageConsumePrefix msg) (cookieMessageConsume msg) := by
  unfold cookieMessageConsumePrefix cookieMessageConsume modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact indexLookupPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem cookieMessageConsumePrefix_preserves (c : AmbientContracts I) (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (cookieMessageConsumePrefix msg) := by
  unfold cookieMessageConsumePrefix
  repeat' first
    | with_reducible exact indexLookupPrefix_preserves_ambient c _ _
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hiddenClock64_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

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

def original (call : CookieCall) : M call.Result := match call with
  | .make src => makeCookie src
  | .create index src mac1 => cookieMessageCreate index src mac1
  | .validate msg src checkCookie => cookieValidatePacket msg src checkCookie
  | .consume msg => cookieMessageConsume msg

def observed (call : CookieCall) : MixedM call.Result := match call with
  | .make src => liftPrefix (makeCookie src)
  | .create index src mac1 => liftPrefix (cookieMessageCreate index src mac1)
  | .validate msg src checkCookie => liftPrefix (cookieValidatePacket msg src checkCookie)
  | .consume msg => cookieMessageConsumePrefix msg

theorem erases (call : CookieCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | make src => exact erasesPrefix_lift _
  | create index src mac1 => exact erasesPrefix_lift _
  | validate msg src checkCookie => exact erasesPrefix_lift _
  | consume msg => exact cookieMessageConsumePrefix_erases msg

theorem preserves_ambient (c : AmbientContracts I) (hc : CookieStable I)
    (call : CookieCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | make src => exact AmbientContracts.drop (cookieLift_spec c hc (fun _ => True) _ (makeCookie_sameCookieKernel src))
  | create index src mac1 => exact AmbientContracts.drop (cookieLift_spec c hc (fun _ => True) _ (cookieMessageCreate_sameCookieKernel index src mac1))
  | validate msg src checkCookie => exact AmbientContracts.drop (cookieLift_spec c hc (fun _ => True) _ (cookieValidatePacket_sameCookieKernel msg src checkCookie))
  | consume msg => exact cookieMessageConsumePrefix_preserves c msg

theorem allocation (call : CookieCall) : PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationCookieStable

end CookieCall
end Leanux.Proofs.WG.Lifetimes
