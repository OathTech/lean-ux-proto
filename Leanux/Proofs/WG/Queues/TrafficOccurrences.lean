import Leanux.Proofs.WG.Queues.TrafficEffects

/-! Positional queries over the existing source paths. These propositions
select an actual receive occurrence; they neither execute a caller nor replace
its observer. Equal-valued items remain distinct at different path positions. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TrafficOccurrences
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def SectionAdmission (cs next : Ledger) (msg : List UInt8) (src : SkbSource)
    (w v : World) (h k : List RxHistory.Event) (c : Carrier) : Prop :=
  ∃ admitted u t r j suffix,
    runPrefix AdmissionSection.enter w h=(.ok ((),u),h) ∧
    AdmissionCaller.Step cs admitted msg src u t h j ∧
    runPrefix RxHistory.pollScheduledInline t j=(.ok ((),r),k) ∧
    k=j++suffix ∧ next=remaining admitted (NapiCarrier.removedPackets suffix) ∧
    runPrefix AdmissionSection.leave r k=(.ok ((),v),k) ∧
    ReceiveEffects.Accepted cs admitted msg src u.wg t.wg u.ambient t.ambient c

theorem section_origin (step : FloodSection.Step cs next msg src w v h k)
    (member : c ∈ next) : c ∈ cs ∨ SectionAdmission cs next msg src w v h k c := by
  obtain ⟨admitted,u,t,r,j,suffix,start,body,poll,hist,ledger,stop⟩ := step
  have before : c ∈ admitted := (List.mem_filter.mp (by simpa only [ledger,remaining] using member)).1
  rcases ReceiveEffects.caller_origin body before with old | accepted
  · exact Or.inl old
  · exact Or.inr ⟨admitted,u,t,r,j,suffix,start,body,poll,hist,ledger,stop,accepted⟩

/-- The selected accepted occurrence is followed by its actual inline poll
and then the supplied conserved continuation. Its suffix begins at the exact
receive return, rather than at an equal-valued event elsewhere. -/
theorem section_fate (selected : SectionAdmission cs next msg src w v h k c)
    (tail : TrafficEffects.Conserved next final k l) :
    ∃ admitted u t j suffix,
      AdmissionCaller.Step cs admitted msg src u t h j ∧
      ReceiveEffects.Accepted cs admitted msg src u.wg t.wg u.ambient t.ambient c ∧
      l=j++suffix ∧ (c ∈ final ∨ c.packet ∈ NapiCarrier.removedPackets suffix) := by
  obtain ⟨admitted,u,t,r,j,removed,start,body,poll,hist,rfl,stop,accepted⟩ := selected
  have rest := TrafficEffects.trans (TrafficEffects.removal hist) tail
  obtain ⟨suffix,hist,kept⟩ := rest
  refine ⟨admitted,u,t,j,suffix,body,accepted,hist,kept c ?_⟩
  rw [ReceiveEffects.accepted_ledger accepted]
  exact List.mem_cons_self

def FloodStepAdmission (family : Nat) (src : SkbSource) (msg : List UInt8)
    (cs next : Ledger) (w v : World) (h k : List RxHistory.Event) (c : Carrier) : Prop :=
  ∃ u,runPrefix (FloodLoop.route family src) w h=(.ok ((),u),h) ∧
    SectionAdmission cs next msg src u v h k c

theorem floodStep_origin (step : FloodLoop.Step family src msg cs next w v h k)
    (member : c ∈ next) : c ∈ cs ∨ FloodStepAdmission family src msg cs next w v h k c := by
  obtain ⟨u,start,body⟩ := step
  rcases section_origin body member with old | selected
  · exact Or.inl old
  · exact Or.inr ⟨u,start,selected⟩

/-- The index is the position in this existing ordered source path. -/
inductive FloodChosen (family : Nat) (src : SkbSource) (c : Carrier) :
    {messages : List (List UInt8)} → {cs : Ledger} → {w : World} → {h : List RxHistory.Event} →
    {next : Ledger} → {v : World} → {k : List RxHistory.Event} →
    FloodLoop.Path family src messages cs w h next v k → Nat → Prop
  | here (step : FloodLoop.Step family src msg cs middle w u h j)
      (tail : FloodLoop.Path family src messages middle u j next v k)
      (selected : FloodStepAdmission family src msg cs middle w u h j c) :
      FloodChosen family src c (.cons step tail) 0
  | later (step : FloodLoop.Step family src msg cs middle w u h j)
      (tail : FloodLoop.Path family src messages middle u j next v k)
      (selected : FloodChosen family src c tail index) :
      FloodChosen family src c (.cons step tail) (index+1)

theorem floodPath_origin (path : FloodLoop.Path family src messages cs w h next v k)
    (member : c ∈ next) : c ∈ cs ∨ ∃ index,FloodChosen family src c path index := by
  induction path with
  | nil => exact Or.inl member
  | cons step tail ih =>
    rcases ih member with old | selected
    · rcases floodStep_origin step old with prior | current
      · exact Or.inl prior
      · exact Or.inr ⟨0,.here step tail current⟩
    · obtain ⟨index,chosen⟩ := selected
      exact Or.inr ⟨index+1,.later step tail chosen⟩

def BatchStepAdmission (d : Device) (cqes : List Int) (item : Env.BatchItem) (out : ForInStep (List Int))
    (cs next : Ledger) (w v : World) (h k : List RxHistory.Event) (c : Carrier) : Prop :=
  match item with
  | .inject family port msg => ∃ src u,
      runPrefix (BatchAccount.injectFront d family port) w h=(.ok (src,u),h) ∧
      SectionAdmission cs next msg src u v h k c ∧ out=.yield (cqes++[(msg.length : Int)])
  | .xmit _ _ _ _ => False

theorem batchStep_origin (step : BatchAccount.Step d cqes item out cs next w v h k)
    (member : c ∈ next) : c ∈ cs ∨ BatchStepAdmission d cqes item out cs next w v h k c := by
  cases item with
  | inject family port msg =>
    obtain ⟨src,u,start,body,result⟩ := step
    rcases section_origin body member with old | selected
    · exact Or.inl old
    · exact Or.inr ⟨src,u,start,selected,result⟩
  | xmit family addr payload opts =>
    obtain ⟨_,suffix,hist,ledger⟩ := step
    exact Or.inl (List.mem_filter.mp (by simpa only [ledger,remaining] using member)).1

/-- Selection follows the actual done/yield shape, including early exit. -/
inductive BatchChosen (d : Device) (c : Carrier) :
    {entries : List Env.BatchItem} → {cqes : List Int} →
    {cs : Ledger} → {w : World} → {h : List RxHistory.Event} → {out : List Int} →
    {next : Ledger} → {v : World} → {k : List RxHistory.Event} →
    BatchAccount.Path d entries cqes cs w h out next v k → Nat → Prop
  | done (step : BatchAccount.Step d cqes item (.done out) cs next w v h k)
      (selected : BatchStepAdmission d cqes item (.done out) cs next w v h k c) :
      BatchChosen d c (.done step) 0
  | here (step : BatchAccount.Step d cqes item (.yield qs) cs middle w u h j)
      (tail : BatchAccount.Path d entries qs middle u j out next v k)
      (selected : BatchStepAdmission d cqes item (.yield qs) cs middle w u h j c) :
      BatchChosen d c (.yield step tail) 0
  | later (step : BatchAccount.Step d cqes item (.yield qs) cs middle w u h j)
      (tail : BatchAccount.Path d entries qs middle u j out next v k)
      (selected : BatchChosen d c tail index) :
      BatchChosen d c (.yield step tail) (index+1)

theorem batchPath_origin (path : BatchAccount.Path d entries cqes cs w h out next v k)
    (member : c ∈ next) : c ∈ cs ∨ ∃ index,BatchChosen d c path index := by
  induction path with
  | nil => exact Or.inl member
  | done step =>
    rcases batchStep_origin step member with old | selected
    · exact Or.inl old
    · exact Or.inr ⟨0,.done step selected⟩
  | yield step tail ih =>
    rcases ih member with old | selected
    · rcases batchStep_origin step old with prior | current
      · exact Or.inl prior
      · exact Or.inr ⟨0,.here step tail current⟩
    · obtain ⟨index,chosen⟩ := selected
      exact Or.inr ⟨index+1,.later step tail chosen⟩

/-- The source-selected receive and its exact returned journal cut, followed
by pending membership or a removal. The lead locates this call inside the
outer source history; selection itself is supplied by the path query below. -/
def Fate (c : Carrier) (final : Ledger) (h k : List RxHistory.Event) : Prop :=
  ∃ msg src cs admitted w v before after lead suffix,
    before=h++lead ∧ AdmissionCaller.Step cs admitted msg src w v before after ∧
    ReceiveEffects.Accepted cs admitted msg src w.wg v.wg w.ambient v.ambient c ∧
    k=after++suffix ∧ (c ∈ final ∨ c.packet ∈ NapiCarrier.removedPackets suffix)

theorem fate_prefix (fate : Fate c final j k) (history : j=h++lead) : Fate c final h k := by
  obtain ⟨msg,src,cs,admitted,w,v,before,after,front,back,old,step,accepted,hist,result⟩ := fate
  exact ⟨msg,src,cs,admitted,w,v,before,after,lead++front,back,
    by rw [old,history,List.append_assoc],step,accepted,hist,result⟩

theorem fate_continue (fate : Fate c middle h j) (tail : TrafficEffects.Conserved middle final j k) :
    Fate c final h k := by
  obtain ⟨msg,src,cs,admitted,w,v,before,after,front,back,old,step,accepted,hist,result⟩ := fate
  obtain ⟨rest,restEq,kept⟩ := tail
  refine ⟨msg,src,cs,admitted,w,v,before,after,front,back++rest,old,step,accepted,
    by rw [restEq,hist,List.append_assoc],?_⟩
  rcases result with pending | removed
  · rcases kept c pending with pending | removed
    · exact Or.inl pending
    · exact Or.inr (by simpa [NapiCarrier.removedPackets,List.filterMap_append] using
        (List.mem_append_right (NapiCarrier.removedPackets back) removed))
  · exact Or.inr (by simpa [NapiCarrier.removedPackets,List.filterMap_append] using
      (List.mem_append_left (NapiCarrier.removedPackets rest) removed))

/-- Every selected flood occurrence has a fate, including one removed before
the entire loop returns. Selection does not require final ledger membership. -/
theorem floodChosen_fate {path : FloodLoop.Path family src messages cs w h next v k}
    (chosen : FloodChosen family src c path index) : Fate c next h k := by
  induction chosen with
  | here step tail selected =>
    obtain ⟨u,start,selected⟩ := selected
    obtain ⟨admitted,a,b,j,suffix,body,accepted,hist,result⟩ :=
      section_fate selected (TrafficEffects.floodPath tail)
    exact ⟨_,_,_,_,_,_,_,_,[],suffix,by simp,body,accepted,hist,result⟩
  | later step tail selected ih =>
    obtain ⟨lead,hist,_⟩ := TrafficEffects.floodStep step
    exact fate_prefix ih hist

theorem batchChosen_fate {path : BatchAccount.Path d entries cqes cs w h out next v k}
    (chosen : BatchChosen d c path index) : Fate c next h k := by
  induction chosen with
  | done step selected =>
    unfold BatchStepAdmission at selected
    split at selected
    ·
      obtain ⟨src,u,start,body,result⟩ := selected
      cases result
    · exact False.elim selected
  | here step tail selected =>
    unfold BatchStepAdmission at selected
    split at selected
    ·
      obtain ⟨src,a,start,selected,result⟩ := selected
      obtain ⟨admitted,b,z,l,suffix,body,accepted,hist,result⟩ :=
        section_fate selected (TrafficEffects.batchPath tail)
      exact ⟨_,_,_,_,_,_,_,_,[],suffix,by simp,body,accepted,hist,result⟩
    · exact False.elim selected
  | later step tail selected ih =>
    obtain ⟨lead,hist,_⟩ := TrafficEffects.batchStep step
    exact fate_prefix ih hist

def FloodAdmission (cs next : Ledger) (count port family : Nat) (messages : List (List UInt8))
    (w v : World) (h k : List RxHistory.Event) (result : Int) (index : Nat) (c : Carrier) : Prop :=
  ∃ src u t j middle suffix, ∃ path : FloodLoop.Path family src (FloodAccount.messages count messages) cs u h middle t j,
    runPrefix (FloodAccount.front family port) w h=(.ok (src,u),h) ∧
    runPrefix FloodAccount.finish t j=(.ok (result,v),k) ∧
    k=j++suffix ∧ next=remaining middle (NapiCarrier.removedPackets suffix) ∧
    FloodChosen family src c path index

theorem flood_origin (outcome : FloodAccount.Outcome cs next count port family messages w v h k result)
    (member : c ∈ next) : c ∈ cs ∨ ∃ index,FloodAdmission cs next count port family messages w v h k result index c := by
  obtain ⟨src,u,t,j,middle,suffix,start,path,done,hist,ledger⟩ := outcome
  have before : c ∈ middle := (List.mem_filter.mp (by simpa only [ledger,remaining] using member)).1
  rcases floodPath_origin path before with old | chosen
  · exact Or.inl old
  · obtain ⟨index,selected⟩ := chosen
    exact Or.inr ⟨index,src,u,t,j,middle,suffix,path,start,done,hist,ledger,selected⟩

theorem flood_fate (selected : FloodAdmission cs next count port family messages w v h k result index c) :
    Fate c next h k := by
  obtain ⟨src,u,t,j,middle,suffix,path,start,done,hist,rfl,chosen⟩ := selected
  exact fate_continue (floodChosen_fate chosen) (TrafficEffects.removal hist)

def BatchAdmission (cs next : Ledger) (entries : List Env.BatchItem)
    (w v : World) (h k : List RxHistory.Event) (result : Int) (index : Nat) (c : Carrier) : Prop :=
  ∃ d cqes u t j middle suffix, ∃ path : BatchAccount.Path d entries [] cs u h cqes middle t j,
    runPrefix BatchAccount.front w h=(.ok (d,u),h) ∧
    runPrefix (BatchAccount.finish entries cqes) t j=(.ok (result,v),k) ∧
    k=j++suffix ∧ next=remaining middle (NapiCarrier.removedPackets suffix) ∧
    BatchChosen d c path index

theorem batch_origin (outcome : BatchAccount.Outcome cs next entries w v h k result)
    (member : c ∈ next) : c ∈ cs ∨ ∃ index,BatchAdmission cs next entries w v h k result index c := by
  obtain ⟨d,cqes,u,t,j,middle,suffix,start,path,done,hist,ledger⟩ := outcome
  have before : c ∈ middle := (List.mem_filter.mp (by simpa only [ledger,remaining] using member)).1
  rcases batchPath_origin path before with old | chosen
  · exact Or.inl old
  · obtain ⟨index,selected⟩ := chosen
    exact Or.inr ⟨index,d,cqes,u,t,j,middle,suffix,path,start,done,hist,ledger,selected⟩

theorem batch_fate (selected : BatchAdmission cs next entries w v h k result index c) :
    Fate c next h k := by
  obtain ⟨d,cqes,u,t,j,middle,suffix,path,start,done,hist,rfl,chosen⟩ := selected
  exact fate_continue (batchChosen_fate chosen) (TrafficEffects.removal hist)

/-- Inject has one receive position. Its actual NET_RX entry/exit and deferred
finish surround this same captured receive; the final ledger includes removals
after the admission, rather than stopping at the intermediate admitted ledger. -/
def InjectAdmission (cs next : Ledger) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) (w v : World)
    (h k : List RxHistory.Event) (result : Int) (c : Carrier) : Prop :=
  ∃ src u t j admitted suffix a b,
    runPrefix (InjectAccount.front family port tos ll dest) w h=(.ok (src,u),h) ∧
    runPrefix AdmissionSection.enter u h=(.ok ((),a),h) ∧
    AdmissionCaller.Step cs admitted msg src a b h j ∧
    runPrefix AdmissionSection.leave b j=(.ok ((),t),j) ∧
    runPrefix (InjectAccount.finish msg) t j=(.ok (result,v),k) ∧
    k=j++suffix ∧ next=remaining admitted (NapiCarrier.removedPackets suffix) ∧
    ReceiveEffects.Accepted cs admitted msg src a.wg b.wg a.ambient b.ambient c

theorem inject_origin (outcome : ConservationSource.InjectFinal cs family port msg tos ll dest w h result v k next)
    (member : c ∈ next) : c ∈ cs ∨ InjectAdmission cs next family port msg tos ll dest w v h k result c := by
  obtain ⟨src,u,t,j,admitted,suffix,start,body,done,hist,ledger⟩ := outcome
  obtain ⟨a,b,enter,receive,leave⟩ := body
  have before : c ∈ admitted := (List.mem_filter.mp (by simpa only [ledger,remaining] using member)).1
  rcases ReceiveEffects.caller_origin receive before with old | accepted
  · exact Or.inl old
  · exact Or.inr ⟨src,u,t,j,admitted,suffix,a,b,start,enter,receive,leave,done,hist,ledger,accepted⟩

theorem inject_fate (selected : InjectAdmission cs next family port msg tos ll dest w v h k result c) :
    Fate c next h k := by
  obtain ⟨src,u,t,j,admitted,suffix,a,b,start,enter,receive,leave,done,hist,rfl,accepted⟩ := selected
  refine ⟨msg,src,cs,admitted,a,b,h,j,[],suffix,by simp,receive,accepted,hist,?_⟩
  apply ConservationAlgebra.pending_or_removed
  rw [ReceiveEffects.accepted_ledger accepted]
  exact List.mem_cons_self

end Leanux.Proofs.WG.Queues.RxCredits.TrafficOccurrences
