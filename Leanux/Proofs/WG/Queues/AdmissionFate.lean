import Leanux.Proofs.WG.Queues.TrafficOccurrences
import Leanux.Proofs.WG.Queues.PollFatePromotion

/-! A selected receive's later removal is tied to its exact completed poll,
with a checked nondelivery or completed Stack call. The history position is
after this receive; membership at another equal-valued event does not suffice.
Allocation/release validity is a separate strengthening of the certificate. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionFate
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

def Removed (c : Carrier) (after history : List RxHistory.Event) : Prop :=
  ∃ pre post n skb stamp,
    history=after++pre++RxHistory.Event.removed n skb stamp::post ∧
    PollCarrier.packetOfStamp stamp=c.packet ∧
    PollFatePromotion.Certificate (after++pre) n skb stamp history

def Fate (c : Carrier) (final : Ledger) (base history : List RxHistory.Event) : Prop :=
  ∃ msg src cs admitted w v before after lead suffix,
    before=base++lead ∧ AdmissionCaller.Step cs admitted msg src w v before after ∧
    ReceiveEffects.Accepted cs admitted msg src w.wg v.wg w.ambient v.ambient c ∧
    history=after++suffix ∧
    (c∈final ∨ Removed c after history)

theorem removal_position (member : p∈NapiCarrier.removedPackets suffix) :
    ∃ pre post n skb stamp,
      suffix=pre++RxHistory.Event.removed n skb stamp::post ∧
      PollCarrier.packetOfStamp stamp=p := by
  obtain ⟨event,mem,value⟩ := List.mem_filterMap.mp member
  obtain ⟨pre,post,hist⟩ := List.mem_iff_append.mp mem
  cases event <;> simp only [NapiCarrier.removed,reduceCtorEq] at value
  case removed n skb stamp=>
    exact ⟨pre,post,n,skb,stamp,hist,Option.some.inj value⟩

theorem classify (source : TrafficOccurrences.Fate c final base history)
    (polls : PollFatePromotion.Inv base history) : Fate c final base history := by
  obtain ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,outcome⟩ := source
  refine ⟨msg,src,cs,admitted,w,v,before,after,lead,suffix,start,step,accepted,finish,?_⟩
  rcases outcome with pending | removed
  · exact Or.inl pending
  · obtain ⟨pre,post,n,skb,stamp,position,identity⟩ := removal_position removed
    obtain ⟨receiveSuffix,receiveHistory⟩ := AdmissionCaller.step_appends step
    have atRemoval : history=after++pre++RxHistory.Event.removed n skb stamp::post := by
      rw [finish,position,List.append_assoc]
    have certified := polls.selected (pre:=lead++receiveSuffix++pre) (post:=post)
      (n:=n) (skb:=skb) (stamp:=stamp) (by
        rw [atRemoval,receiveHistory,start]
        simp only [List.append_assoc])
    refine Or.inr ⟨pre,post,n,skb,stamp,atRemoval,identity,?_⟩
    simpa only [receiveHistory,start,List.append_assoc] using certified

/-- The classification keeps the captured World, prior history and complete
local key, rather than treating a restarted poll ordinal as globally unique. -/
theorem Removed.classified (removed : Removed c after history) :
    ∃ pre post n skb stamp incoming w pid budget result v before localAfter tail,
      history=after++pre++RxHistory.Event.removed n skb stamp::post ∧
      PollCarrier.packetOfStamp stamp=c.packet ∧
      after++pre=incoming++before.map RxHistory.promote ∧
      runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior incoming))=
        (.ok (result,v),RxJoint.seed (RxHistory.prior incoming)++
          (before++RxJoint.Event.removed n skb stamp::localAfter)) ∧
      history=incoming++(before++RxJoint.Event.removed n skb stamp::localAfter).map RxHistory.promote++tail ∧
      PollFatePromotion.Fate (n,skb,stamp) (before++RxJoint.Event.removed n skb stamp::localAfter) := by
  obtain ⟨pre,post,n,skb,stamp,position,identity,certificate⟩ := removed
  obtain ⟨incoming,w,pid,budget,result,v,before,localAfter,tail,cut,run,journal,named⟩ :=
    certificate.classified
  exact ⟨pre,post,n,skb,stamp,incoming,w,pid,budget,result,v,before,localAfter,tail,
    position,identity,cut,run,journal,named⟩

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionFate
