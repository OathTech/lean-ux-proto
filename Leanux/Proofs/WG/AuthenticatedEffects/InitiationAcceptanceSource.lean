import Leanux.Proofs.WG.AuthenticatedEffects.InitiationFront

/-! Native initiation acceptance before the first peer protocol write. A later
consumption-clock Stop cannot erase the fact that Noise, freshness and flood
checks already admitted this input. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues.RxCredits.HandshakeLoans

structure AcceptedInitiation where
  peer : PeerId
  loan : Option PeerId
  ephemeral : Key
  chainingKey : Key
  hash : Key
  timestamp : Key
  priorTimestamp : Key

def initiationAcceptedFinish (msg : Key) (accepted : AcceptedInitiation) : WG.M (Option PeerId) := do
  let pid := accepted.peer
  setPeer pid { (← getPeer pid) with remoteEphemeral := accepted.ephemeral }
  if ← branch .consumeNewerTimestamp (memcmp accepted.timestamp accepted.priorTimestamp == .gt) then
    setPeer pid { (← getPeer pid) with latestTimestamp := accepted.timestamp }
  setPeer pid { (← getPeer pid) with hash := accepted.hash, chainingKey := accepted.chainingKey, remoteIndex := u32le msg 4 }
  let consumption ← hiddenClock64 .consumptionNow
  let last := (← getPeer pid).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
    setPeer pid { (← getPeer pid) with lastInitiationConsumption := consumption }
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
  initiationOut accepted.loan (some pid)

def initiationTailCheck (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    WG.M (Option AcceptedInitiation) := do
  let failed : WG.M (Option AcceptedInitiation) := do
    let _ ← initiationOut peer none
    return none
  let ss ← mixPrecomputedDh ck (← getPeer pid).precomputedStaticStatic
  if ← branch .consumeSsFailed ss.isNone then return ← failed
  let some (ckSs,key) := ss | invariant "unreachable"
  let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
  if ← branch .consumeTimestampFailed ts.isNone then return ← failed
  let some (t,hashT) := ts | invariant "unreachable"
  let p ← getPeer pid
  let replay := memcmp t p.latestTimestamp != .gt
  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let now ← hiddenClock64 .floodNow
  if ← WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt) then
    return ← failed
  return some ⟨pid,peer,e,ckSs,hashT,t,p.latestTimestamp⟩

def initiationAcceptedCheck (msg : Key) : WG.M (Option AcceptedInitiation) := do
  let failed : WG.M (Option AcceptedInitiation) := do
    let _ ← initiationOut none none
    return none
  match ← initiationAuthFront msg with
  | none => failed
  | some (e,ck,s,hash) =>
    let peer ← pubkeyLookup s
    if ← branch .consumeNoPeer peer.isNone then return ← failed
    let some pid := peer | invariant "unreachable"
    initiationTailCheck msg e ck hash peer pid

def initiationAcceptedContinue (msg : Key) : Option AcceptedInitiation → WG.M (Option PeerId)
  | none => pure none
  | some accepted => initiationAcceptedFinish msg accepted

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
    ((do let _ ← initiationOut peer none; pure none) >>= initiationAcceptedContinue msg) =
      initiationOut peer none := by
  unfold initiationOut
  simp only [bind_assoc,pure_bind,initiationAcceptedContinue]
  apply source_bind
  intro failed
  cases failed <;> simp only [Bool.false_eq_true, ↓reduceIte,bind_assoc,pure_bind]

theorem initiationTailCheck_factor (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    initiationTailCheck msg e ck hash peer pid >>= initiationAcceptedContinue msg =
      initiationTail msg e ck hash peer pid := by
  unfold initiationTailCheck initiationTail
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
          simp only [bind_assoc,if_bind]
          apply source_bind
          intro p
          apply source_bind
          intro now
          apply source_bind
          intro rejected
          cases rejected with
          | true => simpa only [↓reduceIte,bind_assoc] using failed_continue msg peer
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte,pure_bind,initiationAcceptedContinue]
            rfl

theorem initiationAcceptedCheck_factor (msg : Key) :
    initiationAcceptedCheck msg >>= initiationAcceptedContinue msg = consumeInitiation msg := by
  rw [initiationAuthFront_factor]
  unfold initiationAcceptedCheck
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
      | some pid => exact initiationTailCheck_factor msg e ck hash (some pid) pid

end Leanux.Proofs.WG.AuthenticatedEffects
