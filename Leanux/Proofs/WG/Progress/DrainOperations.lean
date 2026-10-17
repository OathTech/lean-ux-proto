import Leanux.Proofs.WG.Progress.DrainModel
import Leanux.WG.PeerRemove
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

def drainSelect : WG.M DrainSelection := do
  let d ← getDev
  if d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty then return .drained
  match ← peekUnit .sendWorker with
  | some u => return .send (← resolveUnit .sendWorker u d.sendWorkQueue)
  | none =>
    match ← peekUnit .clearPeerWorker with
    | some u => return .clear (← resolveUnit .clearPeerWorker u d.clearWorkQueue)
    | none =>
      if (← getAmbient).hidden.isSome then
        throw (.hidden s!"a flush of handshake_send_wq must run queued work ({d.sendWorkQueue.length} send, {d.clearWorkQueue.length} clear items), but no section names it")
      match d.sendWorkQueue.head?, d.clearWorkQueue.head? with
      | some pid, _ => return .send pid
      | none, some pid => return .clear pid
      | none, none => return .drained

abbrev DrainLoopState := Option Unit × Unit

def drainSelectedTurn (upTo : Option PeerId) : DrainSelection → WG.M (ForInStep DrainLoopState)
  | .drained => pure (.done (some (), ()))
  | .send pid => do
    runFlushedSendWork pid
    pure (.yield (none, ()))
  | .clear pid => do
    runFlushedClearWork pid
    if upTo == some pid then return .done (some (), ())
    return .yield (none, ())

def drainTurn (upTo : Option PeerId) (_ : Nat) (_ : DrainLoopState) : WG.M (ForInStep DrainLoopState) :=
  drainSelect >>= drainSelectedTurn upTo

def drainFinish (s : DrainLoopState) : WG.M Unit :=
  match s.1 with
  | some result => pure result
  | none => invariant "handshake_send_wq did not drain"

def drainSource (upTo : Option PeerId) : WG.M Unit := do
  let s ← forIn ([:4096] : Std.Legacy.Range) (none, ()) (drainTurn upTo)
  drainFinish s

theorem drain_source (upTo : Option PeerId) :
    drainSource upTo = drainHandshakeSendWq upTo := by
  unfold drainSource drainHandshakeSendWq drainFinish
  congr 1
  congr 1
  funext n s
  simp only [drainTurn, drainSelect, bind_assoc]
  congr 1
  funext d
  split
  · rfl
  · simp only [bind_assoc]
    congr 1
    funext send
    cases send with
    | some u => simp [drainSelectedTurn]
    | none =>
      simp only [bind_assoc]
      congr 1
      funext clear
      cases clear with
      | some u => simp [drainSelectedTurn]
      | none =>
        simp only [bind_assoc]
        congr 1
        funext w
        split
        · rfl
        · cases d.sendWorkQueue.head? <;> cases d.clearWorkQueue.head? <;>
            simp [drainSelectedTurn]

  all_goals (funext s; dsimp +zetaDelta only; cases s.1 <;> rfl)
end Leanux.Proofs.WG.Progress
