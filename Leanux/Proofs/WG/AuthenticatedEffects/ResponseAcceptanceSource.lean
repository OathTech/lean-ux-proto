import Leanux.Proofs.WG.AuthenticatedEffects.InitiationAcceptanceSource

/-! Original response acceptance immediately before its first protocol write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues.RxCredits.HandshakeLoans
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

structure AcceptedResponse where
  peer : PeerId
  ephemeral : Key
  hash : Key
  chainingKey : Key

def responseAcceptedFinish (msg : Key) (r : AcceptedResponse) : WG.M (Option PeerId) := do
  setPeer r.peer {(← getPeer r.peer) with remoteEphemeral := r.ephemeral, hash := r.hash, chainingKey := r.chainingKey, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE}
  return some r.peer

def responseAcceptedContinue (msg : Key) : Option AcceptedResponse → WG.M (Option PeerId)
  | none => pure none
  | some accepted => responseAcceptedFinish msg accepted

def responseTailCheck (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) : WG.M (Option AcceptedResponse) := do
  let fail : WG.M (Option AcceptedResponse) := do
    peerPut (some pid)
    return none
  let p ← getPeer pid
  let state := p.handshakeState
  if ← branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION) then return ← fail
  let eph := (msg.drop 12).take 32
  let (ck,h) ← messageEphemeral true eph p.chainingKey p.hash
  let ee ← mixDh false ck p.ephemeralPrivate eph
  if ← branch .crespEeFailed ee.isNone then return ← fail
  let some (ck,_) := ee | invariant "unreachable"
  let se ← mixDh false ck identity.staticPrivate eph
  if ← branch .crespSeFailed se.isNone then return ← fail
  let some (ck,_) := se | invariant "unreachable"
  let outs ← kdf true true ck p.presharedKey
  let (ck,tempHash,key) := (← kdfOut outs 0,← kdfOut outs 1,← kdfOut outs 2)
  let h := noiseHash (h ++ tempHash)
  let dec ← messageDecrypt ((msg.drop 44).take 16) key h
  if ← branch .crespDecryptFailed dec.isNone then return ← fail
  let some (_,h) := dec | invariant "unreachable"
  if ← branch .crespStateChanged ((← getPeer pid).handshakeState != state) then return ← fail
  return some ⟨pid,eph,h,ck⟩

def responseAcceptedCheck (msg : Key) : WG.M (Option AcceptedResponse) := do
  let identity := (← getDev).staticIdentity
  if ← branch .crespNoIdentity !identity.hasIdentity then return none
  let entry ← indexLookup [.handshake] (u32le msg 8)
  if ← branch .crespNoHandshake entry.isNone then return none
  let some (IndexOwner.handshake _,pid) := entry | invariant "a keypair entry under the handshake mask"
  responseTailCheck msg identity pid

private theorem source_bind {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind {m : Type → Type} [Monad m] (p : Prop) [Decidable p]
    (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl
private theorem invariant_bind (s : String) (f : α → WG.M β) :
    ((invariant s : WG.M α) >>= f) = invariant s := rfl

theorem responseTailCheck_factor (msg : Key) (identity : StaticIdentity) (pid : PeerId) :
    responseTailCheck msg identity pid >>= responseAcceptedContinue msg = responseTail msg identity pid := by
  unfold responseTailCheck responseTail
  simp only [bind_assoc,if_bind]
  repeat' first
    | with_reducible rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp +failIfUnchanged only [bind_assoc,if_bind,pure_bind,responseAcceptedContinue,invariant_bind]
  all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq]
  all_goals repeat' first
    | with_reducible rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp_all +failIfUnchanged [invariant_bind]
  all_goals simp only [responseAcceptedContinue,responseAcceptedFinish,map_eq_pure_bind]

theorem responseAcceptedCheck_factor (msg : Key) :
    responseAcceptedCheck msg >>= responseAcceptedContinue msg = consumeResponse msg := by
  rw [consumeResponse_factor]
  unfold responseAcceptedCheck
  simp only [bind_assoc,if_bind]
  repeat' first
    | exact responseTailCheck_factor msg _ _
    | with_reducible rfl
    | with_reducible apply source_bind
    | intro x
    | split
    | simp +failIfUnchanged only [pure_bind,responseAcceptedContinue,invariant_bind]
  all_goals simp_all only [Option.some.injEq,Prod.mk.injEq,IndexOwner.handshake.injEq]
  all_goals exfalso; rename_i impossible; exact impossible _ _ ⟨rfl,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects
