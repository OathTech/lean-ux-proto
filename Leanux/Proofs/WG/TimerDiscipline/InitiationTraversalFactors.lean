import Leanux.WG.Handshake

/-! Native caller factors shared by the timer observer and finite evaluation.
They do not depend on observer journals or physical frames. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

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

end Leanux.Proofs.WG.TimerDiscipline
