import Leanux.Proofs.WG.Index.DrawRecords

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- The original hidden-input error when the contiguous draw stream runs out. -/
def missingIndexDraw : Stop := .hidden s!"no record left for {HiddenSite.indexDraw.info.label}"

theorem hiddenIndex_empty (ambient : Ambient) (records : ambient.hidden = some []) :
    (AmbientM.hidden .indexDraw).run ambient = .error missingIndexDraw := by
  simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    records, HiddenSite.info, Worker.sectionId, Worker.index, Except.pure, Except.bind, missingIndexDraw]
  rfl

theorem insertStep_empty (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (table : List IndexEntry) (ambient : Ambient) (records : ambient.hidden = some []) :
    ((insertStep owner turn state).run table).run ambient = .error missingIndexDraw := by
  have drawRun : ((hidden .indexDraw : IndexM (List UInt8)).run table).run ambient =
      .error missingIndexDraw := by
    change ((AmbientM.hidden .indexDraw).run ambient).map
      (fun (bytes, after) => ((bytes, table), after)) = _
    rw [hiddenIndex_empty ambient records]
    rfl
  simp only [insertStep, StateT.run_bind, drawRun]
  rfl

/-- With one more turn than colliding records, the next original step reports
missing input. No budget-exhaustion branch or fresh value is fabricated. -/
theorem insertLoop_exhausted (owner : IndexOwner) (table : List IndexEntry) (draws : List Draw)
    (allCollide : ∀ draw ∈ draws, table.any (·.index == draw.value) = true)
    (turns : List Nat) (enough : draws.length < turns.length)
    (ambient : Ambient) (records : ambient.hidden = some (draws.map Draw.record)) :
    ((insertLoop owner turns).run table).run ambient = .error missingIndexDraw := by
  induction draws generalizing turns ambient with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [List.map_nil] at records
      simp only [insertLoop, List.forIn_cons, StateT.run_bind,
        insertStep_empty owner turn (none, ()) table ambient records]
      rfl
  | cons draw draws ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      obtain ⟨⟨result, middle⟩, next, firstRun, value, state, nextRecords⟩ :=
        insertStep_collision owner turn (none, ()) table draw (draws.map Draw.record)
          (allCollide draw (by simp)) ambient records
      subst result
      subst middle
      have restCollide : ∀ r ∈ draws, table.any (·.index == r.value) = true := by
        intro r member
        exact allCollide r (by simp [member])
      have restEnough : draws.length < turns.length := by simpa using enough
      simp only [insertLoop, List.forIn_cons, StateT.run_bind, firstRun]
      exact ih restCollide turns restEnough next nextRecords

theorem indexInsert_exhausted (owner : IndexOwner) (d : Device) (draws : List Draw)
    (allCollide : ∀ draw ∈ draws,
      (removeOwner owner d.indexTable).any (·.index == draw.value) = true)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d)
    (records : ambient.hidden = some (draws.map Draw.record)) :
    ((liftIndex (indexInsert owner)).run g).run ambient = .error missingIndexDraw := by
  let removed := removeOwner owner d.indexTable
  let start := {ambient with steps := ambient.steps.push {
    decision := Decision.idxInsertHashed, outcome := d.indexTable.any (·.owner == owner),
    netRx := ambient.netRxSection}}
  have unhashRun : ((unhashEntry .idxInsertHashed (·.owner == owner)).run d.indexTable).run ambient =
      .ok (((), removed), start) := by
    simp [unhashEntry, removed, removeOwner, start]
    rfl
  have budgetRun : ((recordBudget : IndexM Nat).run removed).run start =
      .ok (((draws.map Draw.record).length + 1, removed), start) := by
    simp [recordBudget, AmbientM.recordBudget, start, records]
    rfl
  have loop : ((forIn ([:(draws.map Draw.record).length + 1] : Std.Legacy.Range)
      (none, ()) (insertStep owner)).run removed).run start = .error missingIndexDraw := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    apply insertLoop_exhausted owner removed draws allCollide _ _ start records
    simp
  have native : ((indexInsert owner).run d.indexTable).run ambient = .error missingIndexDraw := by
    rw [indexInsert_source]
    simp only [StateT.run_bind]
    rw [unhashRun]
    simp only [bind, Except.bind]
    rw [budgetRun]
    dsimp only
    rw [loop]
  rw [liftIndex_run_variant, device]
  simp only [native, Except.map]

end Leanux.Proofs.WG.Index
