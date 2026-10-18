import Leanux.Proofs.WG.AuthenticatedEffects.CookieDispatch
import Leanux.Proofs.Logged.NativeCapture

/-! One receipt for the completed original cookie construction, retained before
the socket reply runs. A receipt means a reply attempt with these bytes and
source, not successful transmission. The original socket path still executes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

structure CookieAttempt where
  input : List UInt8
  source : SkbSource
  creation : WGRunWitness (List UInt8)

def CookieAttempt.Valid (r : CookieAttempt) : Prop :=
  r.creation.Valid (cookieMessageCreate (u32le r.input 4) r.source
    ((r.input.drop (r.input.length - 32)).take 16))

def cookieObserved (msg : List UInt8) (src : SkbSource) : WGPrefix CookieAttempt Unit := do
  let creation ← captureWGRun (cookieMessageCreate (u32le msg 4) src
    ((msg.drop (msg.length - 32)).take 16))
  emitStatePrefix ⟨msg, src, creation⟩
  liftWGPrefix (sendBufferAsReplyToSkb src creation.value)

theorem cookieObserved_run (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List CookieAttempt) :
    runWGPrefix (cookieObserved msg src) w a history =
      match ((cookieMessageCreate (u32le msg 4) src
        ((msg.drop (msg.length - 32)).take 16)).run w).run a with
      | .error e => (.error e, history)
      | .ok ((bytes, v), b) =>
        (((sendBufferAsReplyToSkb src bytes).run v).run b,
          history ++ [⟨msg, src, ⟨bytes, w, v, a, b⟩⟩]) := by
  unfold cookieObserved
  change runStatePrefix _ w a history = _
  rw [runStatePrefix_bind]
  have hc := runWGPrefix_captureWGRun (E := CookieAttempt)
    (cookieMessageCreate (u32le msg 4) src ((msg.drop (msg.length - 32)).take 16)) w a history
  change runStatePrefix _ w a history = _ at hc
  rw [hc]
  cases run : ((cookieMessageCreate (u32le msg 4) src
    ((msg.drop (msg.length - 32)).take 16)).run w).run a with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨bytes,v⟩,b⟩
    simp only [Except.map, runStatePrefix_bind, runStatePrefix_emit]
    rfl

theorem cookieObserved_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (cookieObserved msg src) (sendHandshakeCookie msg src) := by
  intro w a h
  change (runWGPrefix (cookieObserved msg src) w a h).1 = _
  rw [cookieObserved_run]
  unfold sendHandshakeCookie
  simp only [StateT.run_bind]
  cases run : ((cookieMessageCreate (u32le msg 4) src
    ((msg.drop (msg.length - 32)).take 16)).run w).run a with
  | error e => rfl
  | ok out => rcases out with ⟨⟨bytes,v⟩,b⟩; rfl

theorem cookieObserved_receipts (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List CookieAttempt) :
    ∃ suffix, (runWGPrefix (cookieObserved msg src) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.source = src ∧ r.Valid := by
  rw [cookieObserved_run]
  cases run : ((cookieMessageCreate (u32le msg 4) src
    ((msg.drop (msg.length - 32)).take 16)).run w).run a with
  | error e => exact ⟨[], by simp⟩
  | ok out =>
    rcases out with ⟨⟨bytes,v⟩,b⟩
    refine ⟨[⟨msg,src,⟨bytes,w,v,a,b⟩⟩], rfl, by simp, ?_⟩
    intro r mem
    simp only [List.mem_singleton] at mem
    subst r
    exact ⟨rfl,rfl,run⟩

theorem cookieObserved_after_creation (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient) (bytes : List UInt8) (history : List CookieAttempt)
    (created : ((cookieMessageCreate (u32le msg 4) src
      ((msg.drop (msg.length - 32)).take 16)).run w).run a = .ok ((bytes,v),b)) :
    runWGPrefix (cookieObserved msg src) w a history =
      (((sendBufferAsReplyToSkb src bytes).run v).run b,
        history ++ [⟨msg,src,⟨bytes,w,v,a,b⟩⟩]) := by
  rw [cookieObserved_run, created]

end Leanux.Proofs.WG.AuthenticatedEffects
