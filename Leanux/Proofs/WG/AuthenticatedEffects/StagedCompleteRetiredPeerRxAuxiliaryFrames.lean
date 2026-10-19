import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxIngressFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAuxiliaryEntry
import Leanux.Proofs.WG.Queues.AdmissionSection

/-! Exact peer accounting joins the original receive auxiliary proof only on
its identical source occurrence and uniquely selected next carrier ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Auxiliary
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem rebase (hi : Inv initial loans before h w) :
    ∃ suffix,h=before++suffix ∧ Inv (remaining initial (NapiCarrier.removedPackets suffix)) loans h h w := by
  obtain ⟨suffix,history,old⟩ := HolderInitial.rebase hi.1
  exact ⟨suffix,history,old,ExactAt.start (hi.residual history) h⟩

theorem receive_rebase (hi : Inv initial loans before h w)
    (run : runPrefix (AdmissionCaller.receive msg src) w h=(.ok ((),v),k)) :
    ∃ prior next,h=before++prior ∧
      AdmissionCaller.Step (remaining initial (NapiCarrier.removedPackets prior)) next msg src w v h k ∧
      Inv next loans k k v := by
  obtain ⟨prior,next,history,step,after⟩ := AdmissionAuxiliary.receive_rebase hi.1 run
  obtain ⟨epoch,n,j,physical⟩ := hi.1.1.2
  have exactAfter := (hi.residual history).receive_step_restore hi.entry.2.2.2 physical step
  exact ⟨prior,next,history,step,after,ExactAt.start exactAfter k⟩

theorem receive_at_cut (hi : Inv cs loans h h w)
    (step : AdmissionCaller.Step cs next msg src w v h k) : Inv next loans k k v := by
  obtain ⟨prior,actual,history,derived,after⟩ := receive_rebase hi step.1
  have empty : prior=[] := List.append_cancel_left (history.symm.trans (List.append_nil h).symm)
  have unchanged : remaining cs (NapiCarrier.removedPackets [])=cs :=
    List.filter_eq_self.mpr (fun _ _=>rfl)
  simp only [empty,unchanged] at derived
  exact (AdmissionCaller.step_unique step derived) ▸ after

private theorem ambient (action : AmbientM α) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (liftPrefix (monadLift action : Leanux.M α)) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi=>hi.safe)
    (fun _ _ _ same hi=>store hi same)
    (fun _=>productAmbient_spec action _ (fun _ _ hi=>hi))

theorem section_enter : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe AdmissionSection.enter := by
  unfold AdmissionSection.enter
  exact PrefixPreserves.bind (ambient _) (fun _=>ambient _)

theorem section_leave : PrefixPreserves (Inv initial loans before) OwnerChecks.Safe AdmissionSection.leave := by
  unfold AdmissionSection.leave
  exact PrefixPreserves.bind (ambient _) (fun _=>
    PrefixPreserves.bind (ambient _) (fun _=>PrefixPreserves.pure (fun _ _ hi=>hi.safe) ()))

theorem section_normal (hi : Inv initial loans before h w)
    (run : runPrefix (runWorkerPrefix .netRx (AdmissionCaller.receive msg src)) w h=(.ok ((),v),k)) :
    ∃ prior next,h=before++prior ∧
      AdmissionSection.Step (remaining initial (NapiCarrier.removedPackets prior)) next msg src w v h k ∧
      Inv next loans k k v := by
  rw [AdmissionSection.source_factor] at run
  obtain ⟨x,u,j,start,tail⟩ := DecryptIteration.bind_normal run
  cases x
  have same : j=h := by simpa only [start] using AdmissionSection.enter_history w h
  subst j
  have atStart := (section_enter w h hi).choose_spec.2.2
  rw [start] at atStart
  obtain ⟨x,t,l,body,stop⟩ := DecryptIteration.bind_normal tail
  cases x
  have same : k=l := by simpa only [stop] using AdmissionSection.leave_history t l
  subst l
  obtain ⟨prior,next,old,step,atEnd⟩ := receive_rebase atStart body
  have after := (section_leave t k atEnd).choose_spec.2.2
  rw [stop] at after
  exact ⟨prior,next,old,⟨u,t,start,step,stop⟩,after⟩

theorem section_at_cut (hi : Inv cs loans h h w)
    (step : AdmissionSection.Step cs next msg src w v h k) : Inv next loans k k v := by
  obtain ⟨prior,actual,history,derived,after⟩ := section_normal hi step.source
  have empty : prior=[] := List.append_cancel_left (history.symm.trans (List.append_nil h).symm)
  have unchanged : remaining cs (NapiCarrier.removedPackets [])=cs :=
    List.filter_eq_self.mpr (fun _ _=>rfl)
  simp only [empty,unchanged] at derived
  exact (AdmissionSection.Step.unique step derived) ▸ after

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Auxiliary
