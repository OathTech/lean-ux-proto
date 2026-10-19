import Leanux.Proofs.WG.RetirementSecurity.CreateRefusal

/-! Native validity of the refused-return receipts. A marker records entry to
cleanup; the following legacy releases still decide actual disposal and may
stop partway through the batch. -/
namespace Leanux.Proofs.WG.RetirementSecurity.CreateRefusal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits TransmitSecurity

def refusal? : Event→Option Receipt | .refused r=>some r | _=>none

def Good (h : List Event) : Prop := ∀r∈h.filterMap refusal?,r.Valid

theorem front_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (front pid item) (liftWG (createReturnSource pid item)) := by
  unfold front createReturnSource createPublishReturn
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  repeat' first
    | with_reducible exact TxDisposition.enqueue_erases _ _
    | with_reducible exact TxDisposition.publish_erases _ _
    | with_reducible exact TxDisposition.nativeAccess_erases (getPeerMixed_erases _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem embed_good (g : TxDisposition.Obs α) :
    PrefixPreserves (fun h (_:World)=>Good h) Good (embed g) := by
  intro w h before
  obtain ⟨suffix,history⟩ := Appends.focus Event.legacy legacy? g w h
  have same := focusPrefix_other Event.legacy legacy? refusal? (fun _=>rfl) g w h
  have good : Good (runPrefix (embed g) w h).2 := by
    intro r member
    apply before r
    simpa only [embed,same] using member
  refine ⟨suffix,history,good,?_⟩
  cases (runPrefix (embed g) w h).1 <;> trivial

private theorem native_valid (a : WG.M α) (r : RunWitness α)
    (valid : r.Valid (liftWG a)) :
    (WGRunWitness.mk r.value r.before.wg r.after.wg r.before.ambient r.after.ambient).Valid a := by
  change (liftWG a).run r.before=.ok (r.value,r.after) at valid
  rw [liftWG_run] at valid
  cases run : (a.run r.before.wg).run r.before.ambient with
  | error e=>simp [run,Except.map] at valid
  | ok out=>
    obtain ⟨⟨x,g⟩,ambient⟩:=out
    simp only [run,Except.map,Except.ok.injEq,Prod.mk.injEq] at valid
    obtain ⟨hx,hv⟩:=valid
    change (a.run r.before.wg).run r.before.ambient=.ok ((r.value,r.after.wg),r.after.ambient)
    rw [run,hx]
    rw [←congrArg World.wg hv,←congrArg World.ambient hv]

private theorem capture_front (pid : PeerId) (item : List SkbId) :
    PrefixEnsures (fun h (_:World)=>Good h) Good (captureObserved (embed (front pid item)))
      (fun r h _=>Good h ∧ r.Valid (liftWG (createReturnSource pid item))) := by
  apply (PrefixEnsures.captureObserved
    (show PrefixEnsures (fun h (_:World)=>Good h) Good (embed (front pid item))
      (fun _ h _=>Good h) from embed_good (front pid item))).consequence
    (fun _ _ hi=>hi)
  intro r h v post
  obtain ⟨_,good,h0,_,run⟩:=post
  refine ⟨good,?_⟩
  exact (focusPrefix_erases Event.legacy legacy? (front_erases pid item) r.before h0).symm.trans
    (congrArg Prod.fst run)

private theorem branch_rule (site : Decision) (value : Bool) :
    PrefixEnsures (fun h (_:World)=>Good h) Good (liftPrefix (liftWG (branch site value)))
      (fun result h _=>result=value ∧ Good h) := by
  apply PrefixEnsures.lift (P:=fun h (_:World)=>Good h) (S:=Good) _ (fun _ _ hi=>hi)
  intro h w result v before run
  cases run
  exact ⟨rfl,before⟩

private theorem emit_good (r : Receipt) (valid : r.Valid) :
    PrefixPreserves (fun h (_:World)=>Good h) Good (emitPrefix (.refused r)) := by
  intro w h before
  have good : Good (h++[.refused r]) := by
    intro other member
    simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,refusal?,
      List.mem_append,List.mem_singleton] at member
    rcases member with old | equal
    · exact before other old
    · simpa only [equal] using valid
  exact ⟨[.refused r],rfl,good,good⟩

private theorem after_zero_good (pid : PeerId) (item : List SkbId) (first : SkbId) (r : RunWitness Int)
    (head : item.head?=some first) (valid : r.Valid (liftWG (createReturnSource pid item)))
    (zero : r.value≠0) : PrefixPreserves (fun h (_:World)=>Good h) Good (do
      if ← liftPrefix (liftWG (branch .createDataOkEpipe (r.value == -WG.EPIPE))) then return
      emitPrefix (.refused (receipt pid item first r))
      embed (TxDisposition.cleanup pid item first)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (branch_rule .createDataOkEpipe (r.value == -WG.EPIPE))
  intro returned w h input
  obtain ⟨rfl,before⟩:=input
  by_cases pipe : (r.value == -WG.EPIPE)=true
  · simp only [pipe,ite_true]
    exact PrefixPreserves.pure (fun _ _ hi=>hi) () w h before
  · simp only [pipe]
    have rejected : r.value≠-WG.EPIPE := by simpa using pipe
    exact (PrefixPreserves.bind
      (emit_good (receipt pid item first r) ⟨head,native_valid _ r valid,zero,rejected⟩)
      (fun _=>embed_good (TxDisposition.cleanup pid item first))) w h before

theorem tail_good (pid : PeerId) (item : List SkbId) (first : SkbId) (r : RunWitness Int)
    (head : item.head?=some first) (valid : r.Valid (liftWG (createReturnSource pid item))) :
    PrefixPreserves (fun h (_:World)=>Good h) Good (tail pid item first r) := by
  unfold tail
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (branch_rule .createDataOk (r.value == 0))
  intro returned w h input
  obtain ⟨rfl,before⟩:=input
  by_cases zero : (r.value == 0)=true
  · simp only [zero,ite_true]
    exact PrefixPreserves.pure (fun _ _ hi=>hi) () w h before
  · simp only [zero]
    exact after_zero_good pid item first r head valid (by simpa using zero) w h before

/-- Every reached refusal marker has the captured original return prefix and
both actual failed success tests, even if cleanup subsequently stops. -/
theorem good (pid : PeerId) (item : List SkbId) :
    PrefixPreserves (fun h (_:World)=>Good h) Good (observe pid item) := by
  unfold observe
  cases head : item.head? with
  | none=>
    exact (PrefixEnsures.lift (P:=fun h (_:World)=>Good h) (S:=Good) _
      (fun _ _ hi=>hi) (fun _ _ _ _ hi _=>hi)).preserves
  | some first=>
    apply PrefixEnsures.preserves
    apply PrefixEnsures.bind (capture_front pid item)
    intro r w h input
    exact tail_good pid item first r head input.2 w h input.1

/-- Native use records the same valid receipts without exposing synthetic
product components; validity includes actual WG and Ambient endpoints only. -/
theorem native_good (pid : PeerId) (item : List SkbId) :
    StatePrefixPreserves (fun h (_:WGWorld) (_:Ambient)=>Good h) Good (native pid item) := by
  intro w a h before
  obtain ⟨suffix,history,safe,_⟩:=good pid item (NativeAdapter.world w a) h before
  refine ⟨suffix,history,safe,?_⟩
  cases result : (runPrefix ((native pid item).run w) a h).1 with
  | error reason=>trivial
  | ok out=>
    obtain ⟨⟨value,v⟩,b⟩:=out
    exact safe

end Leanux.Proofs.WG.RetirementSecurity.CreateRefusal
