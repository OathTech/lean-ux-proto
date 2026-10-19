import Leanux.Proofs.WG.Queues.AdmissionFate
import Leanux.Proofs.WG.Queues.PollReleaseRunner

/-! Selected admission fates with allocation validity at the actual later
poll input. A removal entails a release in that poll's completed suffix;
the accepted packet may instead remain in the final residual ledger. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

def Removed (c : Carrier) (after history : List RxHistory.Event) : Prop :=
  ∃ pre post n skb stamp,
    history=after++pre++RxHistory.Event.removed n skb stamp::post ∧
    PollCarrier.packetOfStamp stamp=c.packet ∧
    PollReleaseCaller.Certificate (after++pre) n skb stamp history

def Fate (c : Carrier) (final : Ledger) (base history : List RxHistory.Event) : Prop :=
  ∃ msg src cs admitted w v before after lead suffix,
    before=base++lead ∧ AdmissionCaller.Step cs admitted msg src w v before after ∧
    ReceiveEffects.Accepted cs admitted msg src w.wg v.wg w.ambient v.ambient c ∧
    history=after++suffix ∧ (c∈final ∨ Removed c after history)

theorem classify (source : TrafficOccurrences.Fate c final base history)
    (polls : PollReleaseCaller.Certificates base history) : Fate c final base history := by
  obtain ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,outcome⟩ := source
  refine ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,?_⟩
  rcases outcome with pending | removed
  · exact Or.inl pending
  · obtain ⟨pre,post,n,skb,stamp,position,identity⟩ := AdmissionFate.removal_position removed
    obtain ⟨receiveSuffix,receiveHistory⟩ := AdmissionCaller.step_appends step
    have atRemoval : history=after++pre++RxHistory.Event.removed n skb stamp::post := by
      rw [finish,position,List.append_assoc]
    have certified := polls.selected (pre:=lead++receiveSuffix++pre) (post:=post)
      (n:=n) (skb:=skb) (stamp:=stamp) (by
        rw [atRemoval,receiveHistory,start]
        simp only [List.append_assoc])
    refine Or.inr ⟨pre,post,n,skb,stamp,atRemoval,identity,?_⟩
    simpa only [receiveHistory,start,List.append_assoc] using certified

theorem Removed.classified (removed : Removed c after history) : AdmissionFate.Removed c after history := by
  obtain ⟨pre,post,n,skb,stamp,position,identity,certificate⟩ := removed
  exact ⟨pre,post,n,skb,stamp,position,identity,certificate.fate⟩

theorem Fate.classified (fate : Fate c final base history) : AdmissionFate.Fate c final base history := by
  obtain ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,outcome⟩ := fate
  exact ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,
    outcome.imp id Removed.classified⟩

/-- Release and named disposition refer to the same local invocation, key and
fresh suffix. The incoming allocation invariant is retained as evidence. -/
theorem Removed.release (removed : Removed c after history) :
    ∃ pre post n skb stamp incoming w pid budget result v before localAfter tail,
      history=after++pre++RxHistory.Event.removed n skb stamp::post ∧
      PollCarrier.packetOfStamp stamp=c.packet ∧
      after++pre=incoming++before.map RxHistory.promote ∧
      AllocationInv (RxHistory.prior incoming) w.wg ∧
      runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior incoming))=
        (.ok (result,v),RxJoint.seed (RxHistory.prior incoming)++
          (before++RxJoint.Event.removed n skb stamp::localAfter)) ∧
      history=incoming++(before++RxJoint.Event.removed n skb stamp::localAfter).map RxHistory.promote++tail ∧
      RxHistory.Released ((before++RxJoint.Event.removed n skb stamp::localAfter).map RxHistory.promote) stamp ∧
      PollFatePromotion.Fate (n,skb,stamp) (before++RxJoint.Event.removed n skb stamp::localAfter) := by
  obtain ⟨pre,post,n,skb,stamp,position,identity,certificate⟩ := removed
  obtain ⟨incoming,w,pid,budget,result,v,before,localAfter,tail,cut,allocation,run,journal,release⟩ :=
    certificate.release
  refine ⟨pre,post,n,skb,stamp,incoming,w,pid,budget,result,v,before,localAfter,tail,
    position,identity,cut,allocation,run,journal,release,?_⟩
  have named := PollFatePromotion.normal_fate pid budget w v (RxHistory.prior incoming) result
    (congrArg Prod.fst run) (n,skb,stamp) (by
      rw [run]
      exact List.mem_filterMap.mpr ⟨.removed n skb stamp,by simp,rfl⟩)
  have stripped := (pinned_const _private.Leanux.Proofs.WG.Queues.PollFatePromotion.«0».Leanux.Proofs.WG.Queues.RxCredits.PollFatePromotion.Fate.drop_seed)
    (by simpa only [run] using named)
  exact stripped

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionRelease
