import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalModel
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

/-- Original rate check, creation and MAC steps, including their early exits. -/
def initiationTraversalPreludeWith (create : PeerId → WG.M (Option (List UInt8)))
    (pid : PeerId) : WG.M (Option (List UInt8)) := do
  if ← branchExpired .initRateLimited (← getPeer pid).lastSentHandshake REKEY_TIMEOUT (!·) then return none
  let now ← hiddenClock64 .initLastSent
  setPeer pid { (← getPeer pid) with lastSentHandshake := now }
  let created ← create pid
  if ← branch .initCreated created.isSome then
    let some msg := created | invariant "unreachable"
    return some (← addMacToPacket pid msg)
  return none

def initiationTraversalPrelude (pid : PeerId) : WG.M (Option (List UInt8)) :=
  initiationTraversalPreludeWith createInitiation pid

/-- Original remainder after traversal, retaining the final retransmit hook. -/
def initiationTraversalFinishWith (send : PeerId → List UInt8 → WG.M Unit)
    (pid : PeerId) (msg : List UInt8) : WG.M Unit := do
  timersAnyAuthenticatedPacketSent pid
  let now ← hiddenClock64 .initLastSentAgain
  setPeer pid { (← getPeer pid) with lastSentHandshake := now }
  send pid msg
  timersHandshakeInitiated pid

def initiationTraversalFinish (pid : PeerId) (msg : List UInt8) : WG.M Unit :=
  initiationTraversalFinishWith sendBufferToPeer pid msg

def initiationTraversalSuffixWith (finish : PeerId → List UInt8 → WG.M Unit)
    (pid : PeerId) : Option (List UInt8) → WG.M Unit
  | none => pure ()
  | some msg => do timersTraversal pid; finish pid msg

def initiationTraversalSuffix (pid : PeerId) : Option (List UInt8) → WG.M Unit :=
  initiationTraversalSuffixWith initiationTraversalFinish pid

theorem initiationTraversal_source (pid : PeerId) :
    (initiationTraversalPrelude pid >>= initiationTraversalSuffix pid) = sendHandshakeInitiation pid := by
  simp only [initiationTraversalPrelude, initiationTraversalPreludeWith,
    sendHandshakeInitiation, bind_assoc]
  congr 1
  funext peer
  congr 1
  funext limited
  cases limited <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
  · congr 1
    funext now
    congr 1
    funext p
    congr 1
    funext ignored
    congr 1
    funext created
    congr 1
    funext made
    cases made <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind]
    · rfl
    · cases created with
      | none => rfl
      | some msg => simp only [initiationTraversalSuffix, initiationTraversalSuffixWith,
          initiationTraversalFinish, initiationTraversalFinishWith, bind_assoc, pure_bind]
  · rfl

def observedInitiationTraversal (pid : PeerId) : Leanux.M InitiationTraversalCall := do
  let message ← liftWG (initiationTraversalPrelude pid)
  match message with
  | none => return ⟨none, none⟩
  | some msg =>
    let hook ← dataDoneCapture (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)
    liftWG (initiationTraversalFinish pid msg)
    return ⟨some msg, some hook⟩

theorem observedInitiationTraversal_erase (pid : PeerId) :
    (do let _ ← observedInitiationTraversal pid; pure ()) = liftWG (sendHandshakeInitiation pid) := by
  have unit_drop (action : Leanux.M Unit) : (do action; pure ()) = action := by
    funext entry
    change (action.run entry >>= fun out => Except.ok ((), out.2)) = action.run entry
    cases h : action.run entry with
    | error err => rfl
    | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl
  rw [← initiationTraversal_source pid, liftWG_bind_variant]
  simp only [observedInitiationTraversal, bind_assoc]
  congr 1
  funext message
  cases message with
  | none => rfl
  | some msg =>
    simp only [bind_assoc, pure_bind, unit_drop, initiationTraversalSuffix,
      initiationTraversalSuffixWith, liftWG_bind_variant]
    exact dataDoneCapture_bind _ _ _


end Leanux.Proofs.WG.TimerDiscipline
