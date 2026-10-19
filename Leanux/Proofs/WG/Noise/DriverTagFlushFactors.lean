import Leanux.Proofs.WG.Index.FlushFactors

/-! Native factors separated from observer and frame dependencies. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Flush
open Leanux Leanux.WG
universe u

def sendWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (worker : PeerId → m Unit)
    (pid : PeerId) : m Unit := do
  lift (Index.flushedSendPrepare pid)
  let _ ← lift (hidden (.sectionStart .sendWorker))
  worker pid
  let _ ← lift (hidden (.sectionStop .sendWorker))
  pure ()

def clearWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (worker : PeerId → m Unit)
    (pid : PeerId) : m Unit := do
  lift (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
  let _ ← lift (hidden (.sectionStart .clearPeerWorker))
  worker pid
  let _ ← lift (hidden (.sectionStop .clearPeerWorker))
  pure ()


def placeholderWith {m : Type → Type u} [Monad m]
    (send clear : PeerId → m Unit) (d : Device) (upTo : Option PeerId) :
    m (ForInStep (Option Unit × Unit)) := do
  match d.sendWorkQueue.head?, d.clearWorkQueue.head? with
  | some pid, _ =>
    send pid
    pure (.yield (none,()))
  | none, some pid =>
    clear pid
    if upTo == some pid then pure (.done (some (),())) else pure (.yield (none,()))
  | none, none => pure (.done (some (),()))

def turnWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (send clear : PeerId → m Unit)
    (upTo : Option PeerId) : m (ForInStep (Option Unit × Unit)) := do
  let d ← lift getDev
  if d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty then
    return .done (some (),())
  match ← lift (peekUnit .sendWorker) with
  | some u =>
    let pid ← lift (resolveUnit .sendWorker u d.sendWorkQueue)
    send pid
    pure (.yield (none,()))
  | none =>
    match ← lift (peekUnit .clearPeerWorker) with
    | some u =>
      let pid ← lift (resolveUnit .clearPeerWorker u d.clearWorkQueue)
      clear pid
      if upTo == some pid then pure (.done (some (),())) else pure (.yield (none,()))
    | none =>
      if (← lift getAmbient).hidden.isSome then
        lift (throw (.hidden s!"a flush of handshake_send_wq must run queued work ({d.sendWorkQueue.length} send, {d.clearWorkQueue.length} clear items), but no section names it"))
      placeholderWith send clear d upTo

def drainWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (send clear : PeerId → m Unit)
    (upTo : Option PeerId) : m Unit := do
  let out ← forIn ([0:4096] : Std.Legacy.Range) (none,()) (fun _ _ => turnWith lift send clear upTo)
  match out.1 with
  | some value => pure value
  | none => lift (invariant "handshake_send_wq did not drain")

def timersWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α)
    (deleted : PeerId → PeerTimer → m Unit) (drain : Option PeerId → m Unit)
    (pid : PeerId) : m Unit := do
  for t in PeerTimer.all do deleted pid t
  if (← lift getDev).clearWorkQueue.contains pid then drain (some pid)

theorem send_factor (pid : PeerId) :
    runFlushedSendWork pid = sendWith (fun {_} a => a) handshakeSendWorker pid :=
  Index.runFlushedSendWork_factor pid

theorem clear_factor (pid : PeerId) :
    runFlushedClearWork pid = clearWith (fun {_} a => a) queuedExpiredZeroKeyMaterial pid := rfl

theorem drain_factor (upTo : Option PeerId) :
    drainHandshakeSendWq upTo =
      drainWith (fun {_} a => a) runFlushedSendWork runFlushedClearWork upTo := by
  unfold drainHandshakeSendWq drainWith turnWith placeholderWith
  congr 1
  funext out
  rcases out with ⟨returned,_⟩
  cases returned <;> rfl

theorem timers_factor (pid : PeerId) :
    timersStop pid = timersWith (fun {_} a => a) delTimer drainHandshakeSendWq pid := rfl

end Leanux.Proofs.WG.Noise.DriverTags.Flush
