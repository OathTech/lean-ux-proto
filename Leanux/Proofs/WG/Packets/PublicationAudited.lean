import Leanux.Proofs.WG.Packets.PublicationLifecycleJoint
import Leanux.Proofs.WG.Origins.OwnerDeferred

/-! Packet certificates through actual audit-only worker and timer units.
The existing owner contracts retain their conditional saved-peer receipts;
packet transport uses the same erased run and the unchanged consumed projection. -/
namespace Leanux.Proofs.WG.PublicationAudited
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

theorem source (g : AuditM α) (a : Leanux.M α) (erases : ErasesPrefix g a)
    (preserves : ∀ history, Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg) a) :
    PublicationChecks.Preserves (RxHistory.audit g) :=
  PublicationChecks.quiet _ a (Appends.focus _ _ _) (RxHistory.audit_erases erases)
    (focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent
      PublicationChecks.sensitive (fun _ => rfl) g) preserves

/-- The saved-value postcondition belongs to this same owner execution;
the packet proof does not assert allocation validity for an arbitrary snapshot. -/
theorem join_ensures (g : RxHistory.Obs α) (P : World → Prop) (Q : α → World → Prop)
    (owner : PrefixEnsures (fun h w => OwnerChecks.Inv h w ∧ P w) OwnerChecks.Safe g
      (fun x h w => OwnerChecks.Inv h w ∧ Q x w))
    (publication : PublicationChecks.Preserves g) :
    PrefixEnsures (fun h w => PublicationJoint.Inv h w ∧ P w) PublicationJoint.Safe g
      (fun x h w => PublicationJoint.Inv h w ∧ Q x w) := by
  intro w h hi
  obtain ⟨suffix,hs,ownerSafe,ownerPost⟩ := owner w h ⟨hi.1.1,hi.2⟩
  obtain ⟨_,_,packetSafe,packetPost⟩ := publication w h hi.1.2
  refine ⟨suffix,hs,⟨ownerSafe,packetSafe⟩,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out =>
    rw [hr] at ownerPost packetPost
    exact ⟨⟨ownerPost.1,packetPost⟩,ownerPost.2⟩

private theorem product_store (a : Leanux.M α) (frame : SameProductStore a)
    (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) a :=
  (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationFrontierPoll.«0».Leanux.Proofs.WG.PublicationFrontier.product_store)
    a frame history

private theorem ambient (a : AmbientM α) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (monadLift a : Leanux.M α) :=
  productAmbient_spec a _ (fun _ _ hi => hi)

private theorem dev (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (monadLift getDev : Leanux.M Device) :=
  PublicationPoll.native_product _ _ (PublicationFrontier.store_preserves getDev_sameWGStore history)

private theorem send_source (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      Env.runOneSendWorker := by
  unfold Env.runOneSendWorker
  apply preserves_bind (dev history)
  intro d
  cases d.sendWorkQueue.head? with
  | none => exact ambient (AmbientM.invariant _) history
  | some head =>
    dsimp only
    apply preserves_bind (ambient (AmbientM.peekUnit .sendWorker) history)
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (PublicationFrontier.runFlushedSendWork_preserves pid history)
    · exact ambient (AmbientM.resolveUnit _ _ _) history
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift) pid]
      exact PublicationPoll.native_product _ _ (PublicationFrontier.runFlushedSendWork_preserves pid history)

private theorem clear_source (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      Env.runOneClearWorker := by
  unfold Env.runOneClearWorker
  apply preserves_bind (dev history)
  intro d
  cases d.clearWorkQueue.head? with
  | none => exact ambient (AmbientM.invariant _) history
  | some head =>
    dsimp only
    apply preserves_bind (ambient (AmbientM.peekUnit .clearPeerWorker) history)
    intro unit
    cases unit <;> dsimp only
    all_goals apply preserves_bind
    · exact preserves_pure _
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (PublicationFrontier.runFlushedClearWork_preserves pid history)
    · exact ambient (AmbientM.resolveUnit _ _ _) history
    · intro pid
      rw [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedClearWork_lift) pid]
      exact PublicationPoll.native_product _ _ (PublicationFrontier.runFlushedClearWork_preserves pid history)

theorem sendOne : PublicationJoint.Preserves (RxHistory.audit runOneSendWorkerAudit) :=
  PublicationJoint.combine _ OwnerDeferred.sendOne
    (source _ _ runOneSendWorkerAudit_erases send_source)

theorem clearOne : PublicationJoint.Preserves (RxHistory.audit runOneClearWorkerAudit) :=
  PublicationJoint.combine _ OwnerDeferred.clearOne
    (source _ _ runOneClearWorkerAudit_erases clear_source)

theorem saved : PublicationChecks.Preserves (RxHistory.audit getDevSavedAudit) :=
  source _ _ getDevSavedAudit_erases dev

theorem wheel (d : Device) (j : UInt64) :
    PublicationChecks.Preserves (RxHistory.audit (wheelNextDueAudit d j)) :=
  source _ _ (wheelNextDueAudit_erases d j) (fun _ => preserves_pure _)

private theorem getWG_source (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) (getWG : Leanux.M WGWorld) :=
  product_store _ (fun initial => productGetWG_spec (fun s => s = initial)) history

private theorem step_source (b : UInt64) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (Env.requireStepComplete b) := by
  have read := dev history
  have stop (e : Stop) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg) (throw e : Leanux.M Unit) :=
    by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
  routing_tx_source [Env.requireStepComplete] using [read,stop]

private theorem nothing_source (j : UInt64) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (Env.requireNothingDue j) := by
  have read := getWG_source history
  have timer (t : PeerTimer) := product_store _ (timerWorker_sameKernel t) history
  have later (worker : Worker) (unit : Nat) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg) (Env.sectionAppearsLater worker unit) :=
    product_store _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w x v hr
      cases hr
      rfl) history
  have stop (e : Stop) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg) (throw e : Leanux.M Unit) :=
    by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
  have effect {α : Type} (a : AmbientM α) := ambient a history
  routing_tx_source [Env.requireNothingDue] using [read,timer,later,stop,effect]

private theorem section_source (worker : Worker) (body : Leanux.M Unit)
    (history : List RxHistory.Event)
    (hb : Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) body) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (Env.runTimerSection worker body) := by
  have effect {α : Type} (a : AmbientM α) := ambient a history
  routing_tx_source [Env.runTimerSection,Env.runWorker,modifyAmbient,hidden] using [hb,effect]

private theorem dispatch_source (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (timerDispatchUnit worker pid timer we step) := by
  have read := getWG_source history
  have select (t : PeerTimer) := product_store _ (timerWorker_sameKernel t) history
  have complete (b : UInt64) := step_source b history
  have detach (pid : PeerId) (t : PeerTimer) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg) (monadLift (delTimer pid t) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (PublicationFrontier.delTimer_preserves pid t history)
  have sectionSpec (worker : Worker) (pid : PeerId) (t : PeerTimer) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg)
      (Env.runTimerSection worker (monadLift (WG.timerCallback pid t))) :=
    section_source _ _ history (PublicationPoll.native_product _ _ (PublicationFrontier.timerCallback_preserves pid t history))
  have install (s : Option UInt64) := product_store
    (modifyWG fun w => {w with timerPassStep := s})
    (fun initial => productModifyWG_spec (fun v => v = initial) _ (fun _ => rfl)) history
  have stop (e : Stop) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg) (throw e : Leanux.M Unit) :=
    by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
  have effect {α : Type} (a : AmbientM α) := ambient a history
  routing_tx_source [timerDispatchUnit,peekUnit] using [read,select,complete,detach,sectionSpec,install,stop,effect]

private theorem placeholder_source (j : UInt64) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (RxHistory.placeholderTimerPassSource j) := by
  have read := dev history
  have select (t : PeerTimer) := product_store _ (timerWorker_sameKernel t) history
  have detach (pid : PeerId) (t : PeerTimer) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg) (monadLift (delTimer pid t) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (PublicationFrontier.delTimer_preserves pid t history)
  have sectionSpec (worker : Worker) (pid : PeerId) (t : PeerTimer) : Framing.Preserves
      (fun w : World => PublicationFrontier.Inv history w.wg)
      (Env.runTimerSection worker (monadLift (WG.timerCallback pid t))) :=
    section_source _ _ history (PublicationPoll.native_product _ _ (PublicationFrontier.timerCallback_preserves pid t history))
  routing_tx_source [RxHistory.placeholderTimerPassSource] using [read,select,detach,sectionSpec]

theorem stepComplete (b : UInt64) : PublicationJoint.Preserves (RxHistory.audit (requireStepCompleteAudit b)) :=
  PublicationJoint.combine _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.stepComplete) b)
    (source _ _ (requireStepCompleteAudit_erases b) (step_source b))

theorem nothingDue (j : UInt64) : PublicationJoint.Preserves (RxHistory.audit (requireNothingDueAudit j)) :=
  PublicationJoint.combine _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.nothingDue) j)
    (source _ _ (requireNothingDueAudit_erases j) (nothing_source j))

theorem timerDispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    PublicationJoint.Preserves (RxHistory.audit (timerDispatchAudit worker pid timer we step)) :=
  PublicationJoint.combine _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.timerDispatch) worker pid timer we step)
    (source _ _ (timerDispatchAudit_erases worker pid timer we step) (dispatch_source worker pid timer we step))

theorem placeholderPass (j : UInt64) :
    PublicationJoint.Preserves (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  PublicationJoint.combine _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDeferred.«0».Leanux.Proofs.WG.OwnerDeferred.placeholderPass) j)
    (source _ _ (RxHistory.placeholderTimerPass_erases j) (placeholder_source j))

end Leanux.Proofs.WG.PublicationAudited
