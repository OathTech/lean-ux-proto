import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointHook
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointInitialized

/-! The shared worker's prepare child uses the actual canonical preparation
points. Both history projections and the remaining callback are carried from
that source; no caller frame or replacement observation is supplied. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal

theorem project_append (h : List CausalJournal.Event) (suffix : List OriginEvent) :
    project (h++suffix.map encode)=project h++suffix := by
  have encoded : suffix.map encode=(suffix.map Journal.Event.rxOrigin).map CausalJournal.Event.old := by
    rw [List.map_map]
    rfl
  unfold project
  rw [List.filterMap_append,List.filterMap_append]
  congr 1
  rw [encoded,filterMap_encoded CausalJournal.Event.old old? (fun _=>rfl),
    filterMap_encoded Journal.Event.rxOrigin Journal.origin? (fun _=>rfl)]

theorem observed_remainder {α : Type} (body rest : WGPrefix OriginEvent α)
    (w : World) (v : WGWorld) (b : Ambient) (h : List CausalJournal.Event)
    (suffix : List OriginEvent)
    (same : runWGPrefix body w.wg w.ambient (project h)=
      runWGPrefix rest v b (project h++suffix))
    (appends : StateAppends rest) :
    runPrefix (observed body) w h=
      runPrefix (observed rest) {w with wg:=v,ambient:=b} (h++suffix.map encode) := by
  obtain ⟨last,extended⟩:=appends v b (project h++suffix)
  change (runWGPrefix rest v b (project h++suffix)).2=_ at extended
  let result:=(runWGPrefix rest v b (project h++suffix)).1
  have performed : runWGPrefix rest v b (project h++suffix)=
      (result,project h++suffix++last) := Prod.ext rfl extended
  have left := observed_run body w h result (suffix++last)
    (by rw [same,performed,List.append_assoc])
  have right := observed_run rest {w with wg:=v,ambient:=b} (h++suffix.map encode) result last
    (by simpa only [project_append] using performed)
  rw [left,right,List.map_append,List.append_assoc]

inductive RootPoint : World → List CausalJournal.Event → World → List CausalJournal.Event → Prop where
  | source {w : World} {h : List CausalJournal.Event} {site : Site}
      {v : WGWorld} {b : Ambient} {middle : List OriginEvent}
      {remaining : WGPrefix OriginEvent (Option PeerId)}
      (point : Point canonical w.wg w.ambient (project h) site v b middle remaining) :
      RootPoint w h {w with wg:=v,ambient:=b}
        (h++(middle.drop (project h).length).map encode)

/-- Native preparation cuts retain the same complete packet ledger before
and after access and decrypt receipts, including a later stopped callback. -/
theorem RootPoint.accounted
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (point : RootPoint w h u middle) :
    CompleteCarrier.Accounted middle ledger debts locals u.wg := by
  cases point with
  | source point=>
      obtain ⟨suffix,extended,accounted,_⟩:=canonical_point_accounted before point
      simpa only [extended,List.drop_left] using accounted

/-- The remaining shared callback comes from the fixed native source point;
the equality does not introduce a source point or reset its observation. -/
theorem RootPoint.residual (point : RootPoint w h u middle) :
    ∃remaining,runPrefix hooks.prepare w h=runPrefix remaining u middle := by
  cases point with
  | @source site v b middle remaining point=>
      obtain ⟨suffix,extended⟩:=point.appends
      refine ⟨observed remaining,?_⟩
      rw [extended,List.drop_left,hook_source]
      exact observed_remainder _ _ _ _ _ _ suffix (by rw [←extended]; exact point.run)
        point.remaining_appends

noncomputable def remainder (w : World) (h : List CausalJournal.Event)
    (u : World) (middle : List CausalJournal.Event) (point : RootPoint w h u middle) :
    PrefixM CausalJournal.Event (Option PeerId) := Classical.choose point.residual

theorem remainder_run (point : RootPoint w h u middle) :
    runPrefix hooks.prepare w h=runPrefix (remainder w h u middle point) u middle :=
  Classical.choose_spec point.residual

def iterationPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  fun token w h u middle=>match token with
  | .prepare=>RootPoint w h u middle
  | token=>other token w h u middle

noncomputable def prepare_contract
    {native inside : Iteration.Points.ChildPoints} {Good : List CausalJournal.Event → World → Prop}
    (accept : ∀ledger h w,CompleteCarrier.Accounted h ledger [] [] w.wg → Good h w) :
    Iteration.Points.ChildSourceContract (iterationPoints native) (iterationPoints inside) Good .prepare where
  remainder:=remainder
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,accounted⟩:=before.1
    exact accept ledger middle u (point.accounted accounted)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
