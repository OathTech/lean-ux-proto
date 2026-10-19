import Leanux.Proofs.WG.Progress.DispatchRecordSource
import Leanux.Proofs.WG.Progress.RecordedTurn
import Leanux.Proofs.WG.Roaming.HandshakeOverlayStepSource

/-! Normal record effects through the unchanged scheduler turn and original schedule factor. Continuing recorded turns strictly decrease the remaining list; copied trials retain the actual World. This is not a successful-evaluation or global-completion claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem resumeCandidates_retains (records : List HiddenRecord) (stack : Option Worker)
    (candidates : List Activation) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (resumeCandidates stack candidates) := by
  have fail {α : Type} (message : String) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (unsupported message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  unfold resumeCandidates resumeCandidatesWith
  repeat' first
    | with_reducible exact hasWork_retains records _
    | with_reducible exact activation_retains _ records
    | with_reducible exact modifyAmbient_hidden records _ (fun _=>rfl)
    | with_reducible exact fail _
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem scheduleTurn_retains (records : List HiddenRecord) (stack : Option Worker) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (scheduleTurn stack) := by
  have dev : Preserves (fun w : World=>Tail records w.ambient.hidden) (monadLift getDev : Leanux.M Device) :=
    native_product records getDev (native_getDev records)
  have fail {α : Type} (message : String) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (invariant message : Leanux.M α) :=
    product_invariant_retains records message
  have resumed (candidates : List Activation) :
      Preserves (fun w : World=>Tail records w.ambient.hidden)
        (resumeCandidatesWith Env.Activation.run stack candidates) := by
    simpa only [resumeCandidates] using resumeCandidates_retains records stack candidates
  unfold scheduleTurn scheduleTurnWith
  repeat' first
    | with_reducible exact getAmbient_retains records
    | with_reducible exact dev
    | with_reducible exact peek_retains records
    | with_reducible exact dispatch_retains _ records
    | with_reducible exact softirq_retains records
    | with_reducible exact consistentFilter_retains records _
    | with_reducible exact resumed _
    | with_reducible exact fail _
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem schedule_retains (records : List HiddenRecord) (stack : Option Worker) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.schedule stack) := by
  rw [schedule_source]
  apply preserves_bind (recordBudget_retains records)
  intro budget
  apply preserves_bind ?_
  · intro result
    cases result.1
    · apply (hoare_iff_run _ _ _).mpr
      intro before value after pre run
      change ((AmbientM.budgetExhausted "the scheduler loop").run before.ambient >>= _) = _ at run
      dsimp only [AmbientM.budgetExhausted,StateT.run,StateT.bind,get,getThe,
        MonadStateOf.get,StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure] at run
      cases hidden : before.ambient.hidden <;> rw [hidden] at run
      all_goals change Except.error _ = Except.ok _ at run
      all_goals cases run
    · exact preserves_pure _
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    apply list_view_spec (fun w : World=>w.ambient.hidden) (Tail records)
    intro i state
    exact scheduleTurn_retains records stack

theorem softirq_strict_at (records : List HiddenRecord) (before : World) (d : Device)
    (device : before.wg.dev=some d)
    (pending : (d.peers.toList.filterMap (fun (pid,p)=>if p.napiScheduled then some pid else none)).isEmpty=false)
    (present : before.ambient.hidden=some records)
    (next : (records.dropWhile (fun r=>HiddenSite.passive r.site)).head?.map (·.site)=
      some (HiddenSite.sectionStart .netRx).info.id)
    (after : World) (run : Env.napiSoftirq.run before=.ok ((),after)) :
    StrictTail records after.ambient.hidden := by
  have devRun : (monadLift getDev : Leanux.M Device).run before=.ok (d,before) := by
    change (liftWG getDev).run before=_
    rw [Leanux.Proofs.WG.Roaming.HandshakeOverlay.getDev_run,device]
  have hok {α β : Type} (x : α) (f : α→Except Stop β) : (Except.ok x >>= f)=f x := rfl
  have hg (w : World) : (getAmbient : Leanux.M Ambient).run w=.ok (w.ambient,w) := rfl
  change (d.peers.toList.filterMap (fun x=>if x.2.napiScheduled then some x.1 else none)).isEmpty=false at pending
  simp only [Env.napiSoftirq,StateT.run_bind,devRun,hok,pending,
    Bool.false_eq_true,ite_false,hg] at run
  change ((do
    if before.ambient.hidden.isSome && (←peekHiddenSite)!=some (HiddenSite.sectionStart .netRx).info.id then return
    if (d.peers.toList.filterMap (fun (pid,p)=>if p.napiScheduled then some pid else none)).length>1
      then unsupported "NAPI polls of several peers in one softirq"
    Env.runWorker .netRx do
      for pid in d.peers.toList.filterMap (fun (pid,p)=>if p.napiScheduled then some pid else none) do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun pkts=>pkts.forM Env.deliverInner) : Leanux.M Unit).run before)=_ at run
  simp only [present,Option.isSome_some,Bool.true_and,StateT.run_bind,
    cookiePeek_run before records present,hok,next,bne_self_eq_false,Bool.false_eq_true,ite_false] at run
  let stripped := records.dropWhile (fun r=>HiddenSite.passive r.site)
  let middle := {before with ambient:={before.ambient with hidden:=some stripped}}
  have pre : Tail records middle.ambient.hidden := ⟨stripped,rfl,List.dropWhile_suffix _⟩
  have body : Preserves (fun w : World=>Tail records w.ambient.hidden)
      (do for pid in d.peers.toList.filterMap (fun (pid,p)=>if p.napiScheduled then some pid else none) do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun pkts=>pkts.forM Env.deliverInner) : Leanux.M Unit) := by
    simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc,pure_bind]
    apply preserves_bind ?_ (fun _=>preserves_pure _)
    apply list_view_spec (fun w : World=>w.ambient.hidden) (Tail records)
    intro pid state
    exact preserves_bind (rxPoll_retains records pid _) (fun _=>preserves_pure _)
  split at run
  · cases run
  · exact (hoare_iff_run _ _ _).mp (runWorker_strict records .netRx _ body)
      middle () after pre run

theorem resumeCandidates_continue_strict (records : List HiddenRecord)
    (stack : Option Worker) (candidates : List Activation) :
    Hoare (resumeCandidates stack candidates) (fun w=>Tail records w.ambient.hidden)
      (fun result w=>result=turnContinue→StrictTail records w.ambient.hidden) := by
  have no {α : Type} (message : String) (P : World→Prop) (Q : α→World→Prop) :
      Hoare (unsupported message : Leanux.M α) P Q := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  have impossible {α : Type} (action : Leanux.M α) (Q : α→World→Prop) :
      Hoare action (fun _=>False) Q := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    exact pre.elim
  have quiet : Hoare (pure turnReturn : Leanux.M TurnResult)
      (fun w : World=>Tail records w.ambient.hidden)
      (fun result w=>result=turnContinue→StrictTail records w.ambient.hidden) := by
    apply hoare_consequence (hoare_pure turnReturn (fun w : World=>Tail records w.ambient.hidden)) (fun _ hi=>hi)
    intro value final post same
    have impossible : turnReturn=turnContinue:=post.1.symm.trans same
    cases impossible
  cases candidates with
  | nil => exact quiet
  | cons a rest =>
    cases rest with
    | nil =>
      have finish : Hoare (do
          modifyAmbient fun s=>{s with suspended:=s.suspended.filter (·!=a)}
          Activation.run a
          pure turnContinue : Leanux.M TurnResult)
          (fun w=>Tail records w.ambient.hidden)
          (fun result w=>result=turnContinue→StrictTail records w.ambient.hidden) := by
        apply hoare_bind _ _ (modifyAmbient_hidden records (fun s=>{s with suspended:=s.suspended.filter (·!=a)}) (fun _=>rfl))
        intro _
        apply hoare_bind _ _ (activation_after_tail_strict a records)
        intro _
        exact hoare_consequence (preserves_pure turnContinue) (fun _ hi=>hi) (fun _ _ hi _=>hi)
      cases stack with
      | none => exact finish
      | some worker =>
        unfold resumeCandidates resumeCandidatesWith
        apply hoare_bind _ _ (hasWork_retains records _)
        intro busy
        cases busy
        · exact finish
        · exact hoare_bind _ _ (no _ _ (fun _ _=>False))
            (fun _=>impossible _ _)
    | cons b rest =>
      exact hoare_bind _ _ (no _ _ (fun _ _=>False))
        (fun _=>impossible _ _)

theorem scheduleTurn_continue_strict (stack : Option Worker) (records : List HiddenRecord)
    (before after : World) (present : before.ambient.hidden=some records)
    (run : (scheduleTurn stack).run before=.ok (turnContinue,after)) :
    StrictTail records after.ambient.hidden := by
  let rest := records.dropWhile (fun r=>HiddenSite.passive r.site)
  let middle := {before with ambient:={before.ambient with hidden:=some rest}}
  let next := rest.head?.map (·.site)
  have peek : (peekHiddenSite : Leanux.M (Option Nat)).run before=.ok (next,middle) :=
    cookiePeek_run before records present
  have recorded : before.ambient.hidden.isNone=false := by simp only [present,Option.isNone_some]
  have prior : rest.IsSuffix records:=List.dropWhile_suffix _
  have pre : Tail records middle.ambient.hidden:=⟨rest,rfl,prior⟩
  have hok {α β : Type} (x : α) (f : α→Except Stop β) : (Except.ok x >>= f)=f x := rfl
  by_cases started : ∃worker,next.bind sectionOf=some (worker,true)
  · obtain ⟨worker,start⟩:=started
    rw [turn_dispatch stack worker before middle next recorded peek start] at run
    cases dispatchRun : (Env.dispatch worker).run middle with
    | error stop=>rw [dispatchRun] at run; cases run
    | ok out=>
      obtain ⟨accepted,final⟩:=out
      rw [dispatchRun] at run
      cases accepted
      · cases run
      · cases run
        exact ((hoare_iff_run _ _ _).mp (dispatch_record_effect worker records)
          middle true _ pre dispatchRun).2 rfl
  · have noStart : ∀worker,next.bind sectionOf≠some (worker,true):=by
      intro worker selected; exact started ⟨worker,selected⟩
    cases device : middle.wg.dev with
    | none =>
      have hg (w : World) : (getAmbient : Leanux.M Ambient).run w=.ok (w.ambient,w):=rfl
      simp only [scheduleTurn, scheduleTurnWith,StateT.run_bind,hg,hok,recorded,Bool.false_eq_true,ite_false,peek] at run
      cases selected : next.bind sectionOf with
      | none =>
        change ((liftWG getDev).run middle >>= _) = _ at run
        rw [Leanux.Proofs.WG.Roaming.HandshakeOverlay.getDev_run,device] at run
        cases run
      | some pair =>
        obtain ⟨worker,starts⟩:=pair
        cases starts with
        | true=>exact False.elim (noStart worker selected)
        | false=>
          change ((liftWG getDev).run middle >>= _) = _ at run
          rw [Leanux.Proofs.WG.Roaming.HandshakeOverlay.getDev_run,device] at run
          cases run
    | some d =>
      by_cases polling : (next==some (HiddenSite.sectionStart .netRx).info.id &&
          d.peers.toList.any (·.2.napiScheduled))=true
      · rw [turn_napi stack before middle next d recorded peek noStart device polling] at run
        obtain ⟨afterPoll,afterNext,polled,peeked,_⟩:=
          napiTurn_execution middle after turnContinue run
        have guards : (next==some (HiddenSite.sectionStart .netRx).info.id)=true ∧
            d.peers.toList.any (·.2.napiScheduled)=true := by simpa only [Bool.and_eq_true] using polling
        have head : next=some (HiddenSite.sectionStart .netRx).info.id:=by simpa only [beq_iff_eq] using guards.1
        obtain ⟨pair,member,scheduled⟩:=List.any_eq_true.mp guards.2
        have selected : pair.1∈d.peers.toList.filterMap (fun (pid,p)=>if p.napiScheduled then some pid else none) :=
          List.mem_filterMap.mpr ⟨pair,member,by simp only [scheduled,ite_true]⟩
        have pending : (d.peers.toList.filterMap (fun (pid,p)=>if p.napiScheduled then some pid else none)).isEmpty=false := by
          cases shape : d.peers.toList.filterMap (fun (pid,p)=>if p.napiScheduled then some pid else none) with
          | nil=>rw [shape] at selected; contradiction
          | cons p ps=>rfl
        have stable : rest.dropWhile (fun r=>HiddenSite.passive r.site)=rest := by
          have all (xs : List HiddenRecord) :
              (xs.dropWhile (fun r=>HiddenSite.passive r.site)).dropWhile (fun r=>HiddenSite.passive r.site)=
                xs.dropWhile (fun r=>HiddenSite.passive r.site) := by
            induction xs with
            | nil=>rfl
            | cons r rs ih=>
              cases h:HiddenSite.passive r.site
              · simp only [List.dropWhile_cons,h,Bool.false_eq_true,ite_false]
              · simpa only [List.dropWhile_cons,h,ite_true] using ih
          exact all records
        have normalized : (rest.dropWhile (fun r=>HiddenSite.passive r.site)).head?.map (·.site)=
            some (HiddenSite.sectionStart .netRx).info.id := by rw [stable]; exact head
        have strict:=softirq_strict_at rest middle d device pending rfl normalized afterPoll polled
        exact strict_extend prior ((hoare_iff_run _ _ _).mp
          (retain_strict (peekHiddenSite : Leanux.M (Option Nat)) peek_retains rest)
          afterPoll afterNext after strict peeked)
      · have noPoll : (next==some (HiddenSite.sectionStart .netRx).info.id &&
          d.peers.toList.any (·.2.napiScheduled))=false := Bool.eq_false_iff.mpr polling
        rw [turn_resumption stack before middle next d recorded peek noStart device noPoll] at run
        cases trial : (middle.ambient.suspended.filterM Activation.consistent).run middle with
        | error stop=>rw [trial] at run; cases run
        | ok out=>
          obtain ⟨candidates,afterTrial⟩:=out
          have same:=(filter_consistent_result middle.ambient.suspended middle afterTrial candidates trial).1
          subst afterTrial
          rw [trial] at run
          exact (hoare_iff_run _ _ _).mp (resumeCandidates_continue_strict records stack candidates)
            middle turnContinue after pre run rfl

end Leanux.Proofs.WG.Progress.RecordSuffix
