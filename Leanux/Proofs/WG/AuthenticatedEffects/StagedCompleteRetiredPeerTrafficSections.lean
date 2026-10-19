import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficFrames

/-! Every receive-section transition selects its ledger from the original
admission and inline-poll cuts, retaining the paired exact account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem flood_section (hi : Auxiliary.Inv cs loans h h w)
    (run : runPrefix (FloodSection.action msg src) w h=(.ok ((),v),k)) :
    ∃ next,FloodSection.Step cs next msg src w v h k ∧ Auxiliary.Inv next loans k k v := by
  rw [FloodSection.source_factor] at run
  obtain ⟨x,u,j,start,rest⟩ := DecryptIteration.bind_normal run
  cases x
  have same : j=h := by simpa only [start] using AdmissionSection.enter_history w h
  subst j
  have entry := (Auxiliary.section_enter w h hi).choose_spec.2.2
  rw [start] at entry
  obtain ⟨x,t,j,receive,rest⟩ := DecryptIteration.bind_normal rest
  cases x
  obtain ⟨prior,admitted,priorEq,receipt,afterReceive⟩ := Auxiliary.receive_rebase entry receive
  have priorNil : prior=[] := by
    have len := congrArg List.length priorEq
    simp only [List.length_append] at len
    cases prior with
    | nil => rfl
    | cons x xs => simp only [List.length_cons] at len; omega
  have initial : remaining cs (NapiCarrier.removedPackets prior)=cs := by
    subst prior
    exact List.filter_eq_self.mpr (fun _ _=>rfl)
  rw [initial] at receipt
  obtain ⟨x,r,l,poll,stop⟩ := DecryptIteration.bind_normal rest
  cases x
  have same : k=l := by simpa only [stop] using AdmissionSection.leave_history r l
  subst l
  have afterPoll := (inline admitted loans j t j afterReceive).choose_spec.2.2
  rw [poll] at afterPoll
  obtain ⟨suffix,history,rebase⟩ := Auxiliary.rebase afterPoll
  have post := (Auxiliary.section_leave r k rebase).choose_spec.2.2
  rw [stop] at post
  exact ⟨_,⟨admitted,u,t,r,j,suffix,start,receipt,poll,history,rfl,stop⟩,post⟩

theorem flood_section_restore (hi : Auxiliary.Inv cs loans h h w)
    (step : FloodSection.Step cs next msg src w v h k) : Auxiliary.Inv next loans k k v := by
  obtain ⟨other,derived,after⟩ := flood_section hi step.source
  exact (FloodSection.Step.unique step derived) ▸ after

theorem flood_step_restore (hi : Auxiliary.Inv cs loans h h w)
    (step : FloodLoop.Step family src msg cs next w v h k) : Auxiliary.Inv next loans k k v := by
  obtain ⟨u,start,sectionStep⟩ := step
  have after := (route (family:=family) (src:=src) w h hi).choose_spec.2.2
  rw [start] at after
  exact flood_section_restore after sectionStep

theorem flood_path_restore (hi : Auxiliary.Inv cs loans h h w)
    (path : FloodLoop.Path family src messages cs w h next v k) : Auxiliary.Inv next loans k k v := by
  induction path with
  | nil => exact hi
  | cons step tail ih => exact ih (flood_step_restore hi step)

theorem batch_step_restore (hi : Auxiliary.Inv cs loans h h w)
    (step : BatchAccount.Step d cqes item out cs next w v h k) : Auxiliary.Inv next loans k k v := by
  cases item with
  | inject family port msg =>
    obtain ⟨src,u,start,sectionStep,_⟩ := step
    have after := (batch_inject_front (d:=d) (family:=family) (port:=port) w h hi).choose_spec.2.2
    rw [start] at after
    exact flood_section_restore after sectionStep
  | xmit family addr payload opts =>
    obtain ⟨run,suffix,history,rfl⟩ := step
    have after := (batch_xmit (initial:=cs) (loans:=loans) (before:=h) d cqes family addr payload opts w h hi).choose_spec.2.2
    rw [run] at after
    obtain ⟨actual,hist,post⟩ := Auxiliary.rebase after
    have same := List.append_cancel_left (hist.symm.trans history)
    simpa only [same] using post

theorem batch_path_restore (hi : Auxiliary.Inv cs loans h h w)
    (path : BatchAccount.Path d entries cqes cs w h out next v k) : Auxiliary.Inv next loans k k v := by
  induction path with
  | nil => exact hi
  | done step => exact batch_step_restore hi step
  | yield step tail ih => exact ih (batch_step_restore hi step)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
