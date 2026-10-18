import Leanux.Proofs.WG.HandshakeSecurity.ResponderAuditedFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem Global.audited (g : AuditM α) (a : Leanux.M α) (erases : ErasesPrefix g a)
    (preserves : ∀ confirmed, Framing.Preserves (AuditedFrames.State confirmed) a) :
    Global.Preserves (RxHistory.audit g) :=
  Global.quiet _ a (Appends.focus _ _ _) (RxHistory.audit_erases erases)
    (focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent Global.consumer (fun _ => rfl) g) preserves

namespace Joint

theorem sendOne : Preserves (RxHistory.audit runOneSendWorkerAudit) :=
  from_global _ PublicationAudited.sendOne
    (Global.audited _ _ runOneSendWorkerAudit_erases AuditedFrames.sendOne)

theorem clearOne (H1 : H1ResponderCurrentEdges) : Preserves (RxHistory.audit runOneClearWorkerAudit) :=
  from_global _ PublicationAudited.clearOne
    (Global.audited _ _ runOneClearWorkerAudit_erases (AuditedFrames.clearOne H1))

theorem stepComplete (bucket : UInt64) : Preserves (RxHistory.audit (requireStepCompleteAudit bucket)) :=
  from_global _ (PublicationAudited.stepComplete bucket)
    (Global.audited _ _ (requireStepCompleteAudit_erases bucket) (AuditedFrames.stepComplete bucket))

theorem nothingDue (j : UInt64) : Preserves (RxHistory.audit (requireNothingDueAudit j)) :=
  from_global _ (PublicationAudited.nothingDue j)
    (Global.audited _ _ (requireNothingDueAudit_erases j) (AuditedFrames.nothingDue j))

theorem timerDispatch (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) :
    Preserves (RxHistory.audit (timerDispatchAudit worker pid timer we step)) :=
  from_global _ (PublicationAudited.timerDispatch worker pid timer we step)
    (Global.audited _ _ (timerDispatchAudit_erases worker pid timer we step)
      (AuditedFrames.dispatch worker pid timer we step))

theorem placeholderPass (j : UInt64) :
    Preserves (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  from_global _ (PublicationAudited.placeholderPass j)
    (Global.audited _ _ (RxHistory.placeholderTimerPass_erases j) (AuditedFrames.placeholder j))

theorem timerCallback (pid : PeerId) (timer : PeerTimer) :
    Preserves (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) :=
  from_global _ (PublicationJoint.timerCallback pid timer)
    (Global.native_mixed _ _ (timerCallbackPrefix_erases pid timer) (timerCallback_native pid timer))

end Joint
end Leanux.Proofs.WG.HandshakeSecurity.Responder
