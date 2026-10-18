import Leanux.Proofs.WG.AuthenticatedEffects.CookieRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.CookieObservation
import Leanux.Proofs.WG.AuthenticatedEffects.SocketObservation

/-! Actual cookie acceptance is observed after authentication and before its
first cookie-state write. The receipt survives failure in the write/repayment
suffix. No synthetic acceptance or successful final consumer return is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

structure CookieAcceptance where
  input : Key
  peer : PeerId
  checked : WGRunWitness (Option Key)

def CookieAcceptance.Valid (r : CookieAcceptance) : Prop :=
  r.checked.Valid (cookieAuthFront r.input r.peer) ∧ r.checked.value.isSome = true

def acceptedCookieTail (msg : Key) (pid : PeerId) : WGPrefix CookieAcceptance Unit := do
  let checked ← captureWGRun (cookieAuthFront msg pid)
  if checked.value.isSome then emitStatePrefix ⟨msg,pid,checked⟩
  liftWGPrefix (cookieAfterAuth pid checked.value)

theorem acceptedCookieTail_run (msg : Key) (pid : PeerId)
    (w : WGWorld) (a : Ambient) (h : List CookieAcceptance) :
    runWGPrefix (acceptedCookieTail msg pid) w a h =
      match ((cookieAuthFront msg pid).run w).run a with
      | .error err => (.error err,h)
      | .ok ((cookie,u),b) =>
        (((cookieAfterAuth pid cookie).run u).run b,
          if cookie.isSome then h ++ [⟨msg,pid,⟨cookie,w,u,a,b⟩⟩] else h) := by
  unfold acceptedCookieTail
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have capture := runWGPrefix_captureWGRun (E := CookieAcceptance) (cookieAuthFront msg pid) w a h
  change runStatePrefix _ w a h = _ at capture
  rw [capture]
  cases checked : ((cookieAuthFront msg pid).run w).run a with
  | error err => rfl
  | ok out =>
    rcases out with ⟨⟨cookie,u⟩,b⟩
    cases cookie <;> simp only [Except.map,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,↓reduceIte,runStatePrefix_bind,runStatePrefix_emit] <;> rfl

theorem acceptedCookieTail_erases (msg : Key) (pid : PeerId) :
    ErasesStatePrefix (acceptedCookieTail msg pid) (cookieAuthFront msg pid >>= cookieAfterAuth pid) := by
  intro w a h
  change (runWGPrefix (acceptedCookieTail msg pid) w a h).1 = _
  rw [acceptedCookieTail_run,native_bind_run]
  cases checked : ((cookieAuthFront msg pid).run w).run a with
  | error err => rfl
  | ok out => rcases out with ⟨⟨cookie,u⟩,b⟩; rfl

theorem acceptedCookieTail_receipts (msg : Key) (pid : PeerId)
    (w : WGWorld) (a : Ambient) (h : List CookieAcceptance) :
    ∃ suffix, (runWGPrefix (acceptedCookieTail msg pid) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.peer = pid ∧ r.Valid := by
  rw [acceptedCookieTail_run]
  cases checked : ((cookieAuthFront msg pid).run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨cookie,u⟩,b⟩
    cases cookie with
    | none => exact ⟨[],by simp⟩
    | some value =>
      refine ⟨[⟨msg,pid,⟨some value,w,u,a,b⟩⟩],rfl,by simp,?_⟩
      intro r mem
      simp only [List.mem_singleton] at mem
      subst r
      exact ⟨rfl,rfl,checked,rfl⟩

def acceptedCookie (msg : Key) : WGPrefix CookieAcceptance Unit := do
  let entry ← liftWGPrefix (indexLookup [.handshake,.keypair] (u32le msg 4))
  if ← liftWGPrefix (branch .cookieLookupMiss entry.isNone) then return
  let some (_,pid) := entry | liftWGPrefix (invariant "unreachable")
  acceptedCookieTail msg pid

theorem acceptedCookie_erases (msg : Key) :
    ErasesStatePrefix (acceptedCookie msg) (cookieMessageConsume msg) := by
  rw [cookieAuthFront_factor]
  unfold acceptedCookie
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro entry
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro missed
  cases missed <;> simp only [Bool.false_eq_true,↓reduceIte]
  · cases entry with
    | none => exact erasesStatePrefix_lift _
    | some pair => exact acceptedCookieTail_erases msg pair.2
  · exact erasesStatePrefix_pure ()

theorem acceptedCookie_receipts (msg : Key) (w : WGWorld) (a : Ambient)
    (h : List CookieAcceptance) :
    ∃ suffix, (runWGPrefix (acceptedCookie msg) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.Valid := by
  unfold acceptedCookie
  rw [liftWG_bind_run]
  cases lookup : ((indexLookup [.handshake,.keypair] (u32le msg 4)).run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨entry,u⟩,b⟩
    dsimp only
    rw [liftWG_bind_run]
    cases entry with
    | none => exact ⟨[],by simp [branch,AmbientM.branch,runWGPrefix,runStatePrefix]⟩
    | some pair =>
      change ∃ suffix, (runWGPrefix (acceptedCookieTail msg pair.2) u
        (Leanux.Proofs.WG.CounterWindow.record b .cookieLookupMiss false) h).2 = h ++ suffix ∧ _
      obtain ⟨suffix,eq,len,members⟩ := acceptedCookieTail_receipts msg pair.2 u _ h
      exact ⟨suffix,eq,len,fun r mem => ⟨(members r mem).1,(members r mem).2.2⟩⟩

theorem CookieAcceptance.authenticated (r : CookieAcceptance) (valid : r.Valid) :
    ∃ cookie d p, r.checked.value = some cookie ∧ r.checked.before.dev = some d ∧
      d.peers[r.peer]? = some p ∧ p.haveSentMac1 = true ∧
      xchachaDecrypt p.cookieDecryptionKey ((r.input.drop 8).take 24)
        ((r.input.drop 32).take 32) p.lastMac1Sent = some cookie := by
  cases value : r.checked.value with
  | none => simp [CookieAcceptance.Valid,value] at valid
  | some cookie =>
    obtain ⟨d,p,hd,hp,sent,opened⟩ := cookieAuthFront_authenticated r.input r.peer
      r.checked.before r.checked.after r.checked.ambientBefore r.checked.ambientAfter cookie
      (by simpa only [WGRunWitness.Valid,value] using valid.1)
    exact ⟨cookie,d,p,rfl,hd,hp,sent,opened⟩

theorem acceptedCookieTail_retains_before_stop (msg : Key) (pid : PeerId)
    (w u : WGWorld) (a b : Ambient) (cookie : Key) (h : List CookieAcceptance) (err : Stop)
    (checked : ((cookieAuthFront msg pid).run w).run a = .ok ((some cookie,u),b))
    (stopped : ((cookieAfterAuth pid (some cookie)).run u).run b = .error err) :
    runWGPrefix (acceptedCookieTail msg pid) w a h =
      (.error err,h ++ [⟨msg,pid,⟨some cookie,w,u,a,b⟩⟩]) := by
  rw [acceptedCookieTail_run,checked]
  simp only [stopped,Option.isSome_some,↓reduceIte]

theorem receivedCookie_observer_erases (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (h : List CookieAcceptance)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    (runWGPrefix (acceptedCookie msg) w (CounterWindow.record a .hsCookie true) h).1 =
      ((receiveHandshakePacket msg src).run w).run a := by
  rw [receive_cookie_run msg src w a kind]
  exact acceptedCookie_erases msg _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects
