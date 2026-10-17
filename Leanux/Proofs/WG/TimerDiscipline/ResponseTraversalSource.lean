import Leanux.Proofs.WG.TimerDiscipline.ResponseTraversalModel
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

/-- The original continuation after traversal, including deletion, clock/write
and socket send. It remains conditional on the original session result. -/
def responseTraversalFinish (pid : PeerId) (response : Option OutgoingResponseSessionCall) : WG.M Unit := do
  match response with
  | none => pure ()
  | some cut =>
    if cut.session.begun then
      timersAnyAuthenticatedPacketSent pid
      let now ← hiddenClock64 .respLastSentAgain
      setPeer pid { (← getPeer pid) with lastSentHandshake := now }
      sendBufferToPeer pid cut.message

def responseTraversalPrefix (pid : PeerId) : Leanux.M ResponseTraversalCall := do
  let response ← outgoingResponseSessionPrefix pid
  let afterSession ← Campaign2.Product.read
  let traversal ← if (response.map (·.session.begun)).getD false then do
      let hook ← dataDoneCapture (liftWG (timersTraversal pid))
        (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)
      pure (some hook)
    else pure none
  return ⟨response, afterSession, traversal⟩

def observedResponseTraversal (pid : PeerId) : Leanux.M ResponseTraversalCall := do
  let cut ← responseTraversalPrefix pid
  liftWG (responseTraversalFinish pid cut.response)
  return cut

theorem responseTraversalPrefix_source (pid : PeerId) :
    (do let cut ← responseTraversalPrefix pid; liftWG (responseTraversalFinish pid cut.response)) =
      liftWG (sendHandshakeResponse pid) := by
  rw [← outgoingResponseSession_source pid]
  have read_drop {α : Type} (a : Leanux.M α) : (do let _ ← Campaign2.Product.read; a) = a := rfl
  simp only [responseTraversalPrefix, bind_assoc, pure_bind]
  congr 1
  funext response
  cases response with
  | none =>
    simp only [responseTraversalFinish, outgoingResponseSessionSuffix, Option.map_none, Option.getD_none,
      Bool.false_eq_true, ↓reduceIte, pure_bind, read_drop]
    rfl
  | some cut =>
    cases begun : cut.session.begun <;>
      simp [begun, responseTraversalFinish, outgoingResponseSessionSuffix,
        outgoingResponseSessionFinish, read_drop, dataDoneCapture_bind,
        liftWG_bind_variant]

theorem observedResponseTraversal_erase (pid : PeerId) :
    (do let _ ← observedResponseTraversal pid; pure ()) = liftWG (sendHandshakeResponse pid) := by
  have unit_drop (a : Leanux.M Unit) : (do a; pure ()) = a := by
    funext entry
    change (a.run entry >>= fun out => Except.ok ((), out.2)) = a.run entry
    cases h : a.run entry with
    | error err => rfl
    | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl
  simpa only [observedResponseTraversal, bind_assoc, pure_bind, bind_pure] using
    (show (do let cut ← responseTraversalPrefix pid; liftWG (responseTraversalFinish pid cut.response); pure ()) =
      liftWG (sendHandshakeResponse pid) by simpa only [unit_drop] using responseTraversalPrefix_source pid)


end Leanux.Proofs.WG.TimerDiscipline
