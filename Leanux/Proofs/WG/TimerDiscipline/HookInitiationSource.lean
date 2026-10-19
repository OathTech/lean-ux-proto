import Leanux.Proofs.WG.TimerDiscipline.HookTransmitSource
import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalSource

/-! The original initiation prelude is executed once. Only its three actual
hook cuts receive journal adapters; crypto, MAC and sockets stay opaque
original calls. The worker adds its original final reference payment. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.Initiation
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The unchanged timestamp and socket interval between authenticatedSent
and handshakeInitiated. A socket errno remains the caller's ignored result. -/
def sendInterval (pid : PeerId) (msg : List UInt8) : WG.M Unit := do
  let now ← hiddenClock64 .initLastSentAgain
  setPeer pid {(←getPeer pid) with lastSentHandshake := now}
  sendBufferToPeer pid msg

def withHooks {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (hook : Hook → PeerId → m Unit) (pid : PeerId) : m Unit := do
  let message ← step (initiationTraversalPrelude pid)
  match message with
  | none => pure ()
  | some msg =>
    hook .traversal pid
    hook .authenticatedSent pid
    step (sendInterval pid msg)
    hook .handshakeInitiated pid

theorem source (pid : PeerId) :
    withHooks (fun {_} a=>a) action pid = sendHandshakeInitiation pid := by
  rw [←initiationTraversal_source]
  unfold withHooks
  apply bind_congr
  intro message
  cases message <;>
    simp only [initiationTraversalSuffix,initiationTraversalSuffixWith,
      initiationTraversalFinish,initiationTraversalFinishWith,sendInterval,action,bind_assoc]

def observed (pid : PeerId) : WGPrefix Receipt Unit :=
  withHooks (fun {_} a=>liftWGPrefix a) HookJournal.observed pid

theorem erases (pid : PeerId) :
    ErasesStatePrefix (observed pid) (sendHandshakeInitiation pid) := by
  rw [←source]
  unfold observed withHooks
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro message
  cases message
  · exact erasesStatePrefix_pure _
  · exact erasesStatePrefix_bind (observed_erases .traversal pid) (fun _ =>
      erasesStatePrefix_bind (observed_erases .authenticatedSent pid) (fun _ =>
        erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
          observed_erases .handshakeInitiated pid)))

theorem appends (pid : PeerId) : StateAppends (observed pid) := by
  unfold observed withHooks
  apply (StateAppends.lift _).bind
  intro message
  cases message
  · exact StateAppends.pure _
  · exact (observed_appends .traversal pid).bind (fun _ =>
      (observed_appends .authenticatedSent pid).bind (fun _ =>
        (StateAppends.lift _).bind (fun _ =>
          observed_appends .handshakeInitiated pid)))

theorem preserves (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (observed pid) := by
  unfold observed withHooks
  apply (Transmit.quiet _).bind
  intro message
  cases message
  · exact StatePrefixEnsures.pure _ (fun _ _ _ hi=>hi) (fun _ _ _ hi=>hi)
  · exact (observed_preserves .traversal pid).bind (fun _ =>
      (observed_preserves .authenticatedSent pid).bind (fun _ =>
        (Transmit.quiet _).bind (fun _ =>
          observed_preserves .handshakeInitiated pid)))

/-- The actual worker's final peerPut can Stop or delete the peer; either
way it cannot discard the earlier hook journal. -/
def workerObserved (pid : PeerId) : WGPrefix Receipt Unit := do
  observed pid
  liftWGPrefix (peerPut (some pid))

theorem worker_erases (pid : PeerId) :
    ErasesStatePrefix (workerObserved pid) (handshakeSendWorker pid) :=
  erasesStatePrefix_bind (erases pid) (fun _=>erasesStatePrefix_lift _)

theorem worker_appends (pid : PeerId) : StateAppends (workerObserved pid) :=
  (appends pid).bind (fun _=>StateAppends.lift _)

theorem worker_preserves (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (workerObserved pid) :=
  (preserves pid).bind (fun _=>Transmit.quiet _)

/-- The final original reference payment leaves exactly the sender's journal,
including when either the sender or payment stops. -/
theorem worker_history (pid : PeerId) (g : WGWorld) (a : Ambient) (history : List Receipt) :
    (runWGPrefix (workerObserved pid) g a history).2 =
      (runWGPrefix (observed pid) g a history).2 := by
  unfold workerObserved runWGPrefix
  rw [runStatePrefix_bind]
  cases result : runStatePrefix (observed pid) g a history with
  | mk outcome journal =>
    cases outcome with
    | error stop => rfl
    | ok out =>
      obtain ⟨⟨value,current⟩,inputs⟩:=out
      rfl

end Leanux.Proofs.WG.TimerDiscipline.HookJournal.Initiation
