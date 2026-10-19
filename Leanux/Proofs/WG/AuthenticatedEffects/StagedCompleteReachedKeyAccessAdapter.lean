import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedKeyAccessFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseFrames

/-! Exact connection of the fixed key-access points to TX admission's two
history focus layers. Saved native cuts retain the original product-world
fields and the same journal suffix; the observer is never restarted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open Prepare.Points Staged.Obligations StagedTerminalComplete AllocatedObligation

def encode (event : LifetimeEvent) : CausalJournal.Event := txEvent (.access event)
def project (history : List CausalJournal.Event) : List LifetimeEvent :=
  (history.filterMap txEvent?).filterMap TxDisposition.accessEvent
def observed (body : MixedM α) : PrefixM CausalJournal.Event α := Admission.actualOps.access body

theorem encode_quiet (event : LifetimeEvent) : birthPackets (encode event)=[] ∧ Quiet (encode event) :=
  ⟨rfl,fun _=>rfl⟩

theorem project_append (h : List CausalJournal.Event) (suffix : List LifetimeEvent) :
    project (h++suffix.map encode)=project h++suffix := by
  have encoded : suffix.map encode=(suffix.map TxDisposition.Event.access).map txEvent := by
    rw [List.map_map]
    rfl
  unfold project
  rw [List.filterMap_append,List.filterMap_append]
  congr 1
  rw [encoded,filterMap_encoded txEvent txEvent? (fun _=>rfl),
    filterMap_encoded TxDisposition.Event.access TxDisposition.accessEvent (fun _=>rfl)]

theorem observed_run (body : MixedM α) (w : World) (h : List CausalJournal.Event)
    (result : Except Stop ((α×WGWorld)×Ambient)) (suffix : List LifetimeEvent)
    (performed : runWGPrefix body w.wg w.ambient (project h)=(result,project h++suffix)) :
    runPrefix (observed body) w h=
      (result.map (fun ((value,v),a)=>(value,{w with wg:=v,ambient:=a})),h++suffix.map encode) := by
  have lower:=focusPrefix_suffix TxDisposition.Event.access TxDisposition.accessEvent (liftWGObserver body)
    w (h.filterMap txEvent?)
    (result.map (fun ((value,v),a)=>(value,{w with wg:=v,ambient:=a}))) suffix (by
      rw [liftWGObserver_run]
      change ((runWGPrefix body w.wg w.ambient (project h)).1.map _,
        (runWGPrefix body w.wg w.ambient (project h)).2)=_
      rw [performed]
      rfl)
  have upper:=focusPrefix_suffix txEvent txEvent?
    (focusPrefix TxDisposition.Event.access TxDisposition.accessEvent (liftWGObserver body))
    w h _ (suffix.map TxDisposition.Event.access) lower
  change runPrefix (focusPrefix txEvent txEvent?
    (focusPrefix TxDisposition.Event.access TxDisposition.accessEvent (liftWGObserver body))) w h=_
  rw [upper,List.map_map]
  rfl

theorem observed_remainder (body rest : MixedM α) (w : World) (v : WGWorld) (b : Ambient)
    (h : List CausalJournal.Event) (suffix : List LifetimeEvent)
    (same : runWGPrefix body w.wg w.ambient (project h)=runWGPrefix rest v b (project h++suffix))
    (appends : StateAppends rest) :
    runPrefix (observed body) w h=
      runPrefix (observed rest) {w with wg:=v,ambient:=b} (h++suffix.map encode) := by
  obtain ⟨last,extended⟩:=appends v b (project h++suffix)
  change (runWGPrefix rest v b (project h++suffix)).2=_ at extended
  let result:=(runWGPrefix rest v b (project h++suffix)).1
  have performed : runWGPrefix rest v b (project h++suffix)=(result,project h++suffix++last) :=
    Prod.ext rfl extended
  have left:=observed_run body w h result (suffix++last) (by rw [same,performed,List.append_assoc])
  have right:=observed_run rest {w with wg:=v,ambient:=b} (h++suffix.map encode) result last
    (by simpa only [project_append] using performed)
  rw [left,right,List.map_append,List.append_assoc]

inductive RootPoint (kid : Option KeypairId) (now : Bool) :
    World → List CausalJournal.Event → World → List CausalJournal.Event → Prop where
  | source {w : World} {h : List CausalJournal.Event}
      {site : Site} {v : WGWorld} {b : Ambient} {middle : List LifetimeEvent} {remaining : MixedM Unit}
      (point : Point (canonical kid now) w.wg w.ambient (project h) site v b middle remaining) :
      RootPoint kid now w h {w with wg:=v,ambient:=b}
        (h++(middle.drop (project h).length).map encode)

/-- Native key repayment preserves creation's original phase and ledger,
including setters and erasure before their lifetime receipts. -/
theorem RootPoint.live (before : CreatePhase.Live root debts locals pid items h w.wg)
    (point : RootPoint kid now w h u middle) : CreatePhase.Live root debts locals pid items middle u.wg := by
  cases point with
  | source point=>
    obtain ⟨suffix,extended⟩:=point.appends
    rw [extended,List.drop_left]
    apply before.views _ _ _ (point_view point)
    · intro event member
      obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
      exact (encode_quiet source).1
    · intro event member
      obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
      exact (encode_quiet source).2

theorem RootPoint.residual (point : RootPoint kid now w h u middle) :
    ∃remaining,runPrefix (observed (keypairPutPrefix kid now)) w h=runPrefix remaining u middle := by
  cases point with
  | @source site v b middle remaining point=>
    obtain ⟨suffix,extended⟩:=point.appends
    refine ⟨observed remaining,?_⟩
    rw [extended,List.drop_left]
    exact observed_remainder _ _ _ _ _ _ suffix (by rw [←extended]; exact point.run) point.remaining_appends

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
