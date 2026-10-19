import Leanux.Proofs.WG.AuthenticatedEffects.InitiationFront
import Leanux.Proofs.WG.HandshakeSecurity.ReplayClaims

/-! Exact native source cut after both Noise decryptions and the actual peer
read, before the flood-clock read and freshness guard. The prefix includes
lookup borrowing and all early-refusal cleanup. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues.RxCredits.HandshakeLoans AuthenticatedEffects

structure Input where
  ephemeral : Key
  chainingKey : Key
  hash : Key
  timestamp : Key
  loan : Option PeerId
  peer : PeerId
  prior : Peer

def tailPrefix (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    WG.M (Option Input) := do
  let failed : WG.M (Option Input) := do
    let _ ← initiationOut peer none
    return none
  let ss ← mixPrecomputedDh ck (← getPeer pid).precomputedStaticStatic
  if ← branch .consumeSsFailed ss.isNone then return ← failed
  let some (ckSs,key) := ss | invariant "unreachable"
  let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
  if ← branch .consumeTimestampFailed ts.isNone then return ← failed
  let some (t,hashT) := ts | invariant "unreachable"
  let p ← getPeer pid
  return some ⟨e,ckSs,hashT,t,peer,pid,p⟩

def parse (msg : Key) : WG.M (Option Input) := do
  let failed : WG.M (Option Input) := do
    let _ ← initiationOut none none
    return none
  match ← initiationAuthFront msg with
  | none => failed
  | some (e,ck,s,hash) =>
    let peer ← pubkeyLookup s
    if ← branch .consumeNoPeer peer.isNone then return ← failed
    let some pid := peer | invariant "unreachable"
    tailPrefix msg e ck hash peer pid

def continueWith (msg : Key) : Option Input → WG.M (Option PeerId)
  | none => pure none
  | some input => checkedWith (fun a => a) timestampStep msg input.ephemeral
      input.chainingKey input.hash input.timestamp input.loan input.peer input.prior

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl

private theorem failed_continue (msg : Key) (peer : Option PeerId) :
    ((do let _ ← initiationOut peer none; pure none) >>= continueWith msg) =
      initiationOut peer none := by
  unfold initiationOut
  simp only [bind_assoc,pure_bind,continueWith]
  apply source_bind
  intro failed
  cases failed <;> simp only [Bool.false_eq_true, ↓reduceIte,bind_assoc,pure_bind]

theorem tail_factor (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    tailPrefix msg e ck hash peer pid >>= continueWith msg =
      initiationTail msg e ck hash peer pid := by
  unfold tailPrefix initiationTail
  simp only [bind_assoc]
  apply source_bind
  intro p0
  apply source_bind
  intro ss
  simp only [bind_assoc,if_bind]
  apply source_bind
  intro failed
  cases failed with
  | true => simpa only [↓reduceIte,bind_assoc] using failed_continue msg peer
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ss with
    | none => exact invariant_bind _ _
    | some pair =>
      rcases pair with ⟨ckSs,key⟩
      dsimp only
      simp only [bind_assoc,if_bind]
      apply source_bind
      intro ts
      apply source_bind
      intro failed
      cases failed with
      | true => simpa only [↓reduceIte,bind_assoc] using failed_continue msg peer
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases ts with
        | none => exact invariant_bind _ _
        | some pair =>
          rcases pair with ⟨t,hashT⟩
          dsimp only
          simp only [bind_assoc,pure_bind]
          apply source_bind
          intro p
          simp only [continueWith,checkedWith,successWith,timestampStep,writeTimestamp,
            writeEphemeral,writeMaterial,writeConsumption,writeConsumedTag,bind_assoc,if_bind,pure_bind]

theorem source_factor (msg : Key) :
    parse msg >>= continueWith msg = consumeInitiation msg := by
  rw [initiationAuthFront_factor]
  unfold parse
  simp only [bind_assoc]
  apply source_bind
  intro front
  cases front with
  | none => exact failed_continue msg none
  | some result =>
    rcases result with ⟨e,ck,s,hash⟩
    dsimp only
    simp only [bind_assoc]
    apply source_bind
    intro peer
    unfold initiationAfterLookup
    simp only [bind_assoc,if_bind]
    apply source_bind
    intro missed
    cases missed with
    | true => exact failed_continue msg none
    | false =>
      cases peer with
      | none => exact invariant_bind _ _
      | some pid => exact tail_factor msg e ck hash (some pid) pid

/-- This input property follows the native parser to its actual retained-peer
timestamp read. It states no consumer result or downstream effect. -/
def Stale (msg : Key) (w : WGWorld) (a : Ambient) : Prop :=
  ∃ input u b, ((parse msg).run w).run a = .ok ((some input,u),b) ∧
    memcmp input.timestamp input.prior.latestTimestamp ≠ .gt

theorem original_refuses (msg : Key) (w v : WGWorld) (a b : Ambient)
    (value : Option PeerId) (stale : Stale msg w a)
    (run : ((consumeInitiation msg).run w).run a = .ok ((value,v),b)) :
    value = none := by
  obtain ⟨input,u,c,parsed,older⟩ := stale
  rw [← source_factor,AuthenticatedEffects.native_bind_run,parsed] at run
  change ((continueWith msg (some input)).run u).run c = .ok ((value,v),b) at run
  exact (checked_stale_result msg input.ephemeral input.chainingKey input.hash input.timestamp
    input.loan input.peer input.prior u v c b value older run).1

end Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
