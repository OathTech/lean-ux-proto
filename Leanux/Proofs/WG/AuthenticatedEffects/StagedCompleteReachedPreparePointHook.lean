import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointAccounted

/-! Exact connection to the final shared prepare hook. Both focus layers use
the actual incoming history. Their receipts are the original accesses and
native decrypt capture, with no added event or observer restart. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal

variable {α : Type}

def observed (body : WGPrefix OriginEvent α) : PrefixM CausalJournal.Event α :=
  CausalJournal.product (focusPrefix Journal.Event.rxOrigin Journal.origin? (liftWGObserver body))

theorem hook_source : hooks.prepare=observed RxOrigin.prepare := rfl

theorem observed_run (body : WGPrefix OriginEvent α) (w : World) (history : List CausalJournal.Event)
    (result : Outcome α) (suffix : List OriginEvent)
    (performed : runWGPrefix body w.wg w.ambient (project history)=(result,project history++suffix)) :
    runPrefix (observed body) w history=
      (result.map (fun ((value,v),a)=>(value,{w with wg:=v,ambient:=a})),history++suffix.map encode) := by
  have lower := focusPrefix_suffix Journal.Event.rxOrigin Journal.origin? (liftWGObserver body)
    w (history.filterMap old?)
    (result.map (fun ((value,v),a)=>(value,{w with wg:=v,ambient:=a}))) suffix (by
      rw [liftWGObserver_run]
      change ((runWGPrefix body w.wg w.ambient (project history)).1.map _,
        (runWGPrefix body w.wg w.ambient (project history)).2)=_
      rw [performed]
      rfl)
  have upper:=focusPrefix_suffix Event.old old?
    (focusPrefix Journal.Event.rxOrigin Journal.origin? (liftWGObserver body))
    w history _ (suffix.map Journal.Event.rxOrigin) lower
  change runPrefix (focusPrefix Event.old old? (focusPrefix Journal.Event.rxOrigin Journal.origin? (liftWGObserver body))) w history = _
  rw [upper,List.map_map]
  rfl

/-- The original hook's normal and stopped results retain exactly the mapped
native preparation result and the same original lifetime/decrypt receipts. -/
theorem hook_run (w : World) (history : List CausalJournal.Event) :
    runPrefix hooks.prepare w history =
      ((runWGPrefix RxOrigin.prepare w.wg w.ambient (project history)).1.map
        (fun ((value,v),a)=>(value,{w with wg:=v,ambient:=a})),
       history++((runWGPrefix RxOrigin.prepare w.wg w.ambient (project history)).2.drop
         (project history).length).map encode) := by
  obtain ⟨suffix,extended⟩:=canonical.appends w.wg w.ambient (project history)
  change (runWGPrefix RxOrigin.prepare w.wg w.ambient (project history)).2=_ at extended
  rw [hook_source,observed_run _ _ _ _ suffix (Prod.ext rfl extended),extended,List.drop_left]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
