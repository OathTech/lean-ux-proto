import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedDispose
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedCarrier

/-! Source cuts for the completion lifetime observer's rekey helper. The
decision includes its own strict peer borrow; repayment and work publication
remain separate actual callbacks, with all access events retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal LifetimeEffects

def decisionWith [Monad m] (o : Ops m) (pid : PeerId) : m (Option Bool) := do
  if ← o.step (branch .queuedNotRetry true) then
    o.modifyPeer pid fun p => {p with timerHandshakeAttempts := 0}
  let p ← o.peer pid
  if ← o.step (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT not) then return none
  if ← o.step (branch .queuedDead p.isDead) then return none
  o.get pid
  return some (← o.step (branch .queuedAlreadyQueued
    (p.handshakePending && !(← o.step (peekQueuedUnit .sendWorker pid)))))

def installWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  o.modifyPeer pid fun p => {p with handshakePending := true}
  o.step (recordQueued .sendWorker pid)

def suffixWith [Monad m] (o : Ops m) (pid : PeerId) : Option Bool → m Unit
  | none => pure ()
  | some true => o.put (some pid)
  | some false => do installWith o pid; o.append pid

def guardWith [Monad m] (o : Ops m) (pid : PeerId) : m Bool := do
  let current := (← o.peer pid).keypairCurrent
  let send ← andPrefix (o.step (branch .freshKeypair current.isSome)) do
    let some id := current | o.step (invariant "unreachable")
    let k ← o.keypair id
    andPrefix (o.step (branch .freshValid k.sending.isValid)) do
      orPrefix (o.step (branchCmp .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES) k.sendingCounter REKEY_AFTER_MESSAGES)) do
        andPrefix (o.step (branch .freshInitiator k.iAmTheInitiator)) do
          o.step (branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME)
  o.step (branch .freshSend send)

private theorem bind_same [Monad m] (action : m α) (left right : α → m β)
    (same : ∀ value, left value = right value) : (action >>= left) = (action >>= right) :=
  congrArg (fun f => action >>= f) (funext same)

theorem queued_factor [Monad m] [LawfulMonad m] (o : Ops m) (pid : PeerId) :
    queuedWith o pid false = (decisionWith o pid >>= suffixWith o pid) := by
  unfold queuedWith decisionWith
  simp only [Bool.not_false,bind_assoc]
  repeat' first
    | rfl
    | (apply bind_same; intro value)
    | (simp only [pure_bind,bind_assoc])
    | split
  all_goals cases value <;> simp only [suffixWith,installWith,bind_assoc]
  all_goals first | contradiction | exact bind_pure_unit | rfl

theorem fresh_factor [Monad m] [LawfulMonad m] (o : Ops m) (pid : PeerId) :
    freshWith o pid = (guardWith o pid >>= fun send => if send then queuedWith o pid false else pure ()) := by
  unfold freshWith guardWith
  simp only [bind_assoc]
  rfl

theorem decision_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (decisionWith g pid) (decisionWith t pid) := by
  unfold decisionWith
  repeat' lifetime_effects_project h ρ

theorem install_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (installWith g pid) (installWith t pid) := by
  unfold installWith
  repeat' lifetime_effects_project h ρ

theorem guard_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (guardWith g pid) (guardWith t pid) := by
  unfold guardWith
  simp only [andPrefix,orPrefix]
  repeat' lifetime_effects_project h ρ

theorem decision_lifted (pid : PeerId) :
    decisionWith (RawAppend.lifetimeLifted : Ops (WGPrefix E)) pid =
      liftWGPrefix (StagedEntry.Queued.decisionPrefix pid) := by
  unfold decisionWith StagedEntry.Queued.decisionPrefix StagedEntry.Queued.readyPrefix
    StagedEntry.Queued.borrowedDecision
  simp only [RawAppend.lifetimeLifted,StagedEntry.Queued.lift_bind,bind_assoc]
  repeat' first
    | rfl
    | (apply bind_same; intro value)
    | (simp only [StagedEntry.Queued.lift_bind,StagedEntry.Queued.lift_if,
        StagedEntry.Queued.lift_pure,pure_bind,bind_assoc])
    | split
  all_goals cases value <;> first | contradiction | rfl

theorem install_lifted (pid : PeerId) :
    installWith (RawAppend.lifetimeLifted : Ops (WGPrefix E)) pid =
      liftWGPrefix (StagedEntry.Queued.install pid) := by
  simp only [installWith,StagedEntry.Queued.install,RawAppend.lifetimeLifted,StagedEntry.Queued.lift_bind,bind_assoc]

def prefixOps : Ops (WGPrefix CausalJournal.Event) := LifetimeEffects.decorate
  (CompletionEffects.lifetimeBase (CausalJournal.Event.old ∘ Journal.completionEvent)
    CausalJournal.completion?) CausalJournal.scope? CausalJournal.Event.armed CausalJournal.Event.queued

theorem prefix_projects : Ops.Projects ledgerEvent? prefixOps RawAppend.lifetimeLifted :=
  LifetimeEffects.decorate_projects ledgerEvent? _ _
    (RawAppend.lifetime_base_projects ledgerEvent? _ _ (fun _ => rfl))
    _ _ _ (fun _ => rfl) (fun _ => rfl)

theorem decision_actual (pid : PeerId) : decisionWith CausalJournal.completionLifetime pid =
    decisionWith prefixOps pid := rfl
theorem install_actual (pid : PeerId) : installWith CausalJournal.completionLifetime pid =
    installWith prefixOps pid := rfl
theorem guard_actual (pid : PeerId) : guardWith CausalJournal.completionLifetime pid =
    guardWith prefixOps pid := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
