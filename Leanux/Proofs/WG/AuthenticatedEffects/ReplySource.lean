import Leanux.Proofs.WG.AuthenticatedEffects.CookieObservation

/-! The native reply path factored immediately before its single socket call.
The front contains every original address, allocation and family guard. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.CounterWindow

structure ReplyTarget where
  endpoint : Endpoint
  ipv4 : Bool

def replyFront (src : SkbSource) : WG.M (Option ReplyTarget) := do
  if ← branch .replyInSkbNull false then invariant "a cookie reply without an skb"
  let endpoint ← endpointFromSkb src
  if ← branch .replyEndpointErr endpoint.isNone then
    invariant "a cookie reply to an skb that is neither IPv4 nor IPv6"
  let some e := endpoint | invariant "unreachable"
  if ← branch .replyNoMem !(← hiddenAlloc .replySkb) then return none
  if ← branch .replyInet (e.family == AF_INET) then return some ⟨e,true⟩
  else if ← branch .replyInet6 (e.family == AF_INET6) then return some ⟨e,false⟩
  return none

def replySocket (target : ReplyTarget) (bytes : List UInt8) : WG.M Unit := do
  if target.ipv4 then discard <| send4 target.endpoint none bytes 0 false
  else discard <| send6 target.endpoint none bytes 0 false

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)

private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl

private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl

theorem reply_factor (src : SkbSource) (bytes : List UInt8) :
    sendBufferAsReplyToSkb src bytes = (do
      match ← replyFront src with
      | none => pure ()
      | some target => replySocket target bytes) := by
  unfold sendBufferAsReplyToSkb replyFront replySocket
  simp only [bind_assoc, if_bind, invariant_bind]
  repeat' first
    | rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp only [bind_assoc, if_bind, pure_bind, ↓reduceIte]
  all_goals simp_all [discard]
  all_goals rfl

structure ReplyAttempt where
  source : SkbSource
  bytes : List UInt8
  target : ReplyTarget
  front : WGRunWitness (Option ReplyTarget)

def ReplyAttempt.Valid (r : ReplyAttempt) : Prop :=
  r.front.Valid (replyFront r.source) ∧ r.front.value = some r.target

def replyObserved (src : SkbSource) (bytes : List UInt8) : WGPrefix ReplyAttempt Unit := do
  let front ← captureWGRun (replyFront src)
  match front.value with
  | none => pure ()
  | some target =>
    emitStatePrefix ⟨src,bytes,target,front⟩
    liftWGPrefix (replySocket target bytes)

theorem replyObserved_run (src : SkbSource) (bytes : List UInt8)
    (w : WGWorld) (a : Ambient) (h : List ReplyAttempt) :
    runWGPrefix (replyObserved src bytes) w a h =
      match ((replyFront src).run w).run a with
      | .error e => (.error e,h)
      | .ok ((none,v),b) => (.ok (((),v),b),h)
      | .ok ((some target,v),b) =>
        (((replySocket target bytes).run v).run b,
          h ++ [⟨src,bytes,target,⟨some target,w,v,a,b⟩⟩]) := by
  unfold replyObserved
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have hc := runWGPrefix_captureWGRun (E := ReplyAttempt) (replyFront src) w a h
  change runStatePrefix _ w a h = _ at hc
  rw [hc]
  cases run : ((replyFront src).run w).run a with
  | error e => rfl
  | ok out =>
    rcases out with ⟨⟨target,v⟩,b⟩
    cases target with
    | none => rfl
    | some t =>
      simp only [Except.map, runStatePrefix_bind, runStatePrefix_emit]
      rfl

theorem replyObserved_erases (src : SkbSource) (bytes : List UInt8) :
    ErasesStatePrefix (replyObserved src bytes) (sendBufferAsReplyToSkb src bytes) := by
  intro w a h
  change (runWGPrefix (replyObserved src bytes) w a h).1 = _
  rw [replyObserved_run,reply_factor]
  simp only [StateT.run_bind]
  cases run : ((replyFront src).run w).run a with
  | error e => rfl
  | ok out => rcases out with ⟨⟨target,v⟩,b⟩; cases target <;> rfl

theorem replyObserved_receipts (src : SkbSource) (bytes : List UInt8)
    (w : WGWorld) (a : Ambient) (h : List ReplyAttempt) :
    ∃ suffix, (runWGPrefix (replyObserved src bytes) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.source = src ∧ r.bytes = bytes ∧ r.Valid := by
  rw [replyObserved_run]
  cases run : ((replyFront src).run w).run a with
  | error e => exact ⟨[], by simp⟩
  | ok out =>
    rcases out with ⟨⟨target,v⟩,b⟩
    cases target with
    | none => exact ⟨[], by simp⟩
    | some t =>
      refine ⟨[⟨src,bytes,t,⟨some t,w,v,a,b⟩⟩], rfl, by simp, ?_⟩
      intro r mem
      simp only [List.mem_singleton] at mem
      subst r
      exact ⟨rfl,rfl,run,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects
