import Leanux.Proofs.WG.HandshakeSecurity.ResponderWorkFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.AuditedFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

abbrev State (confirmed : List Nat) (w : World) := History.Native confirmed w.wg

theorem store (a : Leanux.M α) (frame : SameProductStore a) (confirmed : List Nat) :
    Preserves (State confirmed) a := native_product_store frame confirmed

theorem ambient (a : AmbientM α) (confirmed : List Nat) :
    Preserves (State confirmed) (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

theorem dev (confirmed : List Nat) : Preserves (State confirmed) (monadLift getDev : Leanux.M Device) :=
  PublicationPoll.native_product _ _ (native_store getDev_sameWGStore confirmed)

theorem world (confirmed : List Nat) : Preserves (State confirmed) (getWG : Leanux.M WGWorld) :=
  store _ (fun initial => productGetWG_spec (fun s => s = initial)) confirmed

theorem sendOne (confirmed : List Nat) : Preserves (State confirmed) Env.runOneSendWorker := by
  unfold Env.runOneSendWorker
  apply preserves_bind (dev confirmed)
  intro d
  cases d.sendWorkQueue.head? with
  | none => exact ambient (AmbientM.invariant _) confirmed
  | some head =>
    dsimp only
    apply preserves_bind (ambient (AmbientM.peekUnit .sendWorker) confirmed)
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushedSend_native pid confirmed)
    · exact ambient (AmbientM.resolveUnit _ _ _) confirmed
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushedSend_native pid confirmed)

theorem clearOne (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Preserves (State confirmed) Env.runOneClearWorker := by
  unfold Env.runOneClearWorker
  apply preserves_bind (dev confirmed)
  intro d
  cases d.clearWorkQueue.head? with
  | none => exact ambient (AmbientM.invariant _) confirmed
  | some head =>
    dsimp only
    apply preserves_bind (ambient (AmbientM.peekUnit .clearPeerWorker) confirmed)
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushedClear_native H1 pid confirmed)
    · exact ambient (AmbientM.resolveUnit _ _ _) confirmed
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (flushedClear_native H1 pid confirmed)

theorem stepComplete (bucket : UInt64) (confirmed : List Nat) :
    Preserves (State confirmed) (Env.requireStepComplete bucket) := by
  have read := dev confirmed
  have stop (e : Stop) : Preserves (State confirmed) (throw e : Leanux.M Unit) := hoare_throw e
  routing_tx_source [Env.requireStepComplete] using [read, stop]

theorem nothingDue (j : UInt64) (confirmed : List Nat) :
    Preserves (State confirmed) (Env.requireNothingDue j) := by
  have read := world confirmed
  have timer (t : PeerTimer) := store _ (timerWorker_sameKernel t) confirmed
  have later (worker : Worker) (unit : Nat) :
      Preserves (State confirmed) (Env.sectionAppearsLater worker unit) :=
    store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl) confirmed
  have stop (e : Stop) : Preserves (State confirmed) (throw e : Leanux.M Unit) := hoare_throw e
  have effect {α : Type} (a : AmbientM α) := ambient a confirmed
  routing_tx_source [Env.requireNothingDue] using [read, timer, later, stop, effect]

theorem timerSection (worker : Worker) (body : Leanux.M Unit) (confirmed : List Nat)
    (keeps : Preserves (State confirmed) body) :
    Preserves (State confirmed) (Env.runTimerSection worker body) := by
  have effect {α : Type} (a : AmbientM α) := ambient a confirmed
  routing_tx_source [Env.runTimerSection, Env.runWorker, modifyAmbient, hidden] using [keeps, effect]

theorem dispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (confirmed : List Nat) :
    Preserves (State confirmed) (timerDispatchUnit worker pid timer we step) := by
  have read := world confirmed
  have select (t : PeerTimer) := store _ (timerWorker_sameKernel t) confirmed
  have complete (b : UInt64) := stepComplete b confirmed
  have detach (pid : PeerId) (t : PeerTimer) :
      Preserves (State confirmed) (monadLift (delTimer pid t) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (delTimer_native pid t confirmed)
  have callback (worker : Worker) (pid : PeerId) (t : PeerTimer) :
      Preserves (State confirmed) (Env.runTimerSection worker (monadLift (timerCallback pid t))) :=
    timerSection _ _ confirmed (PublicationPoll.native_product _ _ (timerCallback_native pid t confirmed))
  have install (s : Option UInt64) := store (modifyWG fun w => {w with timerPassStep := s})
    (fun initial => productModifyWG_spec (fun v => v = initial) _ (fun _ => rfl)) confirmed
  have stop (e : Stop) : Preserves (State confirmed) (throw e : Leanux.M Unit) := hoare_throw e
  have effect {α : Type} (a : AmbientM α) := ambient a confirmed
  routing_tx_source [timerDispatchUnit, peekUnit] using [read, select, complete, detach, callback, install, stop, effect]

theorem placeholder (j : UInt64) (confirmed : List Nat) :
    Preserves (State confirmed) (RxHistory.placeholderTimerPassSource j) := by
  have read := dev confirmed
  have select (t : PeerTimer) := store _ (timerWorker_sameKernel t) confirmed
  have detach (pid : PeerId) (t : PeerTimer) :
      Preserves (State confirmed) (monadLift (delTimer pid t) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (delTimer_native pid t confirmed)
  have callback (worker : Worker) (pid : PeerId) (t : PeerTimer) :
      Preserves (State confirmed) (Env.runTimerSection worker (monadLift (timerCallback pid t))) :=
    timerSection _ _ confirmed (PublicationPoll.native_product _ _ (timerCallback_native pid t confirmed))
  routing_tx_source [RxHistory.placeholderTimerPassSource] using [read, select, detach, callback]

end Leanux.Proofs.WG.HandshakeSecurity.Responder.AuditedFrames
