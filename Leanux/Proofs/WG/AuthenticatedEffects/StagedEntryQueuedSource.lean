import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRestoreSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationFrames

/-! The queued-initiation suffix has one silent native decision prefix. A
successful borrow precedes either its nonfinal repayment or work publication;
the original branch and ambient-read order is retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open HandshakeSecurity.StagedDisposal

def readyPrefix (pid : PeerId) : WG.M (Option Peer) := do
  if ← branch .queuedNotRetry true then
    setPeer pid {(← getPeer pid) with timerHandshakeAttempts := 0}
  let p ← getPeer pid
  if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return none
  if ← branch .queuedDead p.isDead then return none
  return some p

def borrowedDecision (pid : PeerId) (pending : Bool) : WG.M (Option Bool) := do
  peerGet pid
  return some (← branch .queuedAlreadyQueued
    (pending && !(← peekQueuedUnit .sendWorker pid)))

def decisionPrefix (pid : PeerId) : WG.M (Option Bool) := do
  match ← readyPrefix pid with
  | none => pure none
  | some p => borrowedDecision pid p.handshakePending

def install (pid : PeerId) : WG.M Unit := do
  setPeer pid {(← getPeer pid) with handshakePending := true}
  recordQueued .sendWorker pid

def suffix (pid : PeerId) : Option Bool → WGPrefix CausalJournal.Event Unit
  | none => pure ()
  | some true => CausalJournal.peerRelease (some pid)
  | some false => do
    liftWGPrefix (install pid)
    CausalJournal.effects.append pid

theorem lift_bind (action : WG.M α) (next : α → WG.M β) :
    (liftWGPrefix (action >>= next) : WGPrefix E β) =
      (liftWGPrefix action >>= fun x => liftWGPrefix (next x)) := by
  funext w a h
  change runWGPrefix (liftWGPrefix (_ >>= _)) w a h = runWGPrefix (_ >>= _) w a h
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift,StateT.run_bind]
  cases (action.run w).run a with
  | error _ => rfl
  | ok out => obtain ⟨⟨x,v⟩,b⟩ := out; rfl

theorem lift_if (p : Prop) [Decidable p] (yes no : WG.M α) :
    (liftWGPrefix (if p then yes else no) : WGPrefix E α) =
      if p then liftWGPrefix yes else liftWGPrefix no := by split <;> rfl

theorem lift_pure (value : α) : (liftWGPrefix (pure value) : WGPrefix E α) = pure value := rfl

theorem bind_same (action : WGPrefix E α) (left right : α → WGPrefix E β)
    (same : ∀ value, left value = right value) : (action >>= left) = (action >>= right) := by
  have functions : left = right := funext same
  rw [functions]

theorem factor (pid : PeerId) :
    Effects.queuedWith CausalJournal.effects CausalJournal.peerRelease pid false =
      (liftWGPrefix (decisionPrefix pid) >>= suffix pid) := by
  unfold Effects.queuedWith decisionPrefix readyPrefix borrowedDecision
  simp only [CausalJournal.effects,CausalEffects.ops,TimerEffects.observed,lift_bind,bind_assoc,lift_if]
  repeat' first
    | rfl
    | (simp only [lift_bind,bind_assoc,lift_pure,pure_bind])
    | split
    | (apply bind_same; intro value)
  all_goals cases value <;> simp only [suffix,install,lift_bind,bind_assoc]
  all_goals first | contradiction | exact bind_pure_unit | rfl

/-- Exact source boundary, including a stopped prefix before any effect
receipt. A returned decision continues in the same world and ambient state. -/
theorem run (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event) :
    runWGPrefix (Effects.queuedWith CausalJournal.effects CausalJournal.peerRelease pid false) w a h =
      match ((decisionPrefix pid).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((decision,v),b) => runWGPrefix (suffix pid decision) v b h := by
  rw [factor]
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  cases ((decisionPrefix pid).run w).run a <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queued
