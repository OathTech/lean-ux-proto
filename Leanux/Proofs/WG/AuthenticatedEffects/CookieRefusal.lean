import Leanux.Proofs.WG.AuthenticatedEffects.ResponseRefusal

/-! Cookie authentication is read-only before the authenticated cookie write.
Failure continues through the original reference repayment. The successful
lookup loan remains an explicit obligation of the native caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Cookies
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def cookieAuthFront (msg : Key) (pid : PeerId) : WG.M (Option Key) := do
  let p ← getPeer pid
  if ← branch .cookieNoMac1Sent !p.haveSentMac1 then return none
  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
    ((msg.drop 32).take 32) p.lastMac1Sent
  if ← branch .cookieDecryptOk cookie.isSome then
    let some c := cookie | invariant "unreachable"
    return some c
  return none

def cookieAfterAuth (pid : PeerId) (cookie : Option Key) : WG.M Unit := do
  if let some c := cookie then
    let birthdate ← hiddenClock64 .cookieBirthdate
    setPeer pid { (← getPeer pid) with cookie := c, cookieBirthdate := birthdate, cookieIsValid := true, haveSentMac1 := false }
  peerPut (some pid)

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl

theorem cookieAuthFront_factor (msg : Key) : cookieMessageConsume msg = (do
    let entry ← indexLookup [.handshake,.keypair] (u32le msg 4)
    if ← branch .cookieLookupMiss entry.isNone then return
    let some (_,pid) := entry | invariant "unreachable"
    cookieAuthFront msg pid >>= cookieAfterAuth pid) := by
  unfold cookieMessageConsume cookieAuthFront cookieAfterAuth
  simp only [bind_assoc,if_bind]
  repeat' first
    | with_reducible rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp only [pure_bind,invariant_bind]
  all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq]
  all_goals try solve | exfalso; rename_i impossible; exact impossible _ _ ⟨rfl,rfl⟩
  all_goals repeat' first
    | with_reducible rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp_all

theorem cookieAuthFront_same_world (msg : Key) (pid : PeerId) :
    SameView (id : WGWorld → WGWorld) (cookieAuthFront msg pid) := by
  intro initial
  change Preserves (fun w : WGWorld => w = initial) _
  have read : Preserves (fun w => w = initial) (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    rw [(Leanux.Proofs.WG.Queues.getPeer_normal pid w v p a b run).1]
    exact hi
  unfold cookieAuthFront
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | with_reducible exact read
    | (cookie_source_lift AmbientM; exact hoare_liftAmbient _ _)
    | cookie_source_step

theorem cookieAuthFront_authenticated (msg : Key) (pid : PeerId)
    (w u : WGWorld) (a b : Ambient) (cookie : Key)
    (run : ((cookieAuthFront msg pid).run w).run a = .ok ((some cookie,u),b)) :
    ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ p.haveSentMac1 = true ∧
      xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
        ((msg.drop 32).take 32) p.lastMac1Sent = some cookie := by
  unfold cookieAuthFront at run
  rw [native_bind_run] at run
  cases read : ((getPeer pid).run w).run a with
  | error err => simp [read] at run
  | ok out =>
    rcases out with ⟨⟨p,q⟩,c⟩
    obtain ⟨rfl,rfl,d,hd,hp⟩ := Leanux.Proofs.WG.Queues.getPeer_normal pid w q p a c read
    rw [read] at run
    cases sent : p.haveSentMac1 <;>
      simp [branch,branch_run,sent,StateT.run_bind] at run
    case true =>
      cases opened : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
          ((msg.drop 32).take 32) p.lastMac1Sent with
      | none => simp [opened] at run
      | some plaintext =>
        simp [opened] at run
        obtain ⟨⟨same,_⟩,_⟩ := run
        exact ⟨d,p,hd,hp,sent,opened.trans (congrArg some same)⟩

theorem cookie_refusal_after_lookup (msg : Key) (w u q v : WGWorld)
    (owner : IndexOwner) (pid : PeerId) (a b c d : Ambient)
    (lookup : ((indexLookup [.handshake,.keypair] (u32le msg 4)).run w).run a =
      .ok ((some (owner,pid),u),b))
    (front : ((cookieAuthFront msg pid).run u).run (record b .cookieLookupMiss false) =
      .ok ((none,q),c))
    (borrowed : PeerBorrow.Borrowed (wgStoreView w) (some pid) (wgStoreView u))
    (paid : ((peerPut (some pid)).run q).run c = .ok (((),v),d)) :
    ((cookieMessageConsume msg).run w).run a = .ok (((),v),d) ∧
      PeerBorrow.view v = PeerBorrow.view w ∧ v.sent = w.sent := by
  have world := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieAuthFront_same_world msg pid) u _ none q c front
  change q = u at world
  subst q
  have run : ((cookieMessageConsume msg).run w).run a = .ok (((),v),d) := by
    rw [cookieAuthFront_factor,native_bind_run,lookup]
    change ((cookieAuthFront msg pid >>= cookieAfterAuth pid).run u).run
      (record b .cookieLookupMiss false) = _
    rw [native_bind_run,front]
    exact paid
  refine ⟨run,?_,?_⟩
  · exact (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.repay_spec (some pid) (wgStoreView w))
      u c () v d borrowed paid
  · exact (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (cookieMessageConsume_sent msg) w a () v d run

theorem receive_cookie_run (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((cookieMessageConsume msg).run w).run (record a .hsCookie true) := by
  rw [receive_factor]
  simp [kind,StateT.run_bind,branch,branch_run]

theorem receive_cookie_sent (msg : Key) (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    v.sent = w.sent := by
  rw [receive_cookie_run msg src w a kind] at run
  exact (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieMessageConsume_sent msg) w _ () v b run

end Leanux.Proofs.WG.AuthenticatedEffects
