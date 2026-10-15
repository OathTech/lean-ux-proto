import Leanux.Proofs.WG.Index.DrawRecords

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- The original hidden-input error when the contiguous draw stream runs out. -/
def missingIndexDraw : Stop := .hidden s!"no record left for {HiddenSite.indexDraw.info.label}"

theorem hiddenIndex_empty (w : World) (records : w.hidden = some []) :
    (hidden .indexDraw).run w = .error missingIndexDraw := by
  simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    records, HiddenSite.info, Worker.sectionId, Worker.index, Except.pure, Except.bind, missingIndexDraw]
  rfl

theorem insertStep_empty (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (w : World) (records : w.hidden = some []) :
    (insertStep owner turn state).run w = .error missingIndexDraw := by
  simp only [insertStep, StateT.run_bind, hiddenIndex_empty w records]
  rfl

/-- With one more turn than colliding records, the next original step reports
missing input. No budget-exhaustion branch or fresh value is fabricated. -/
theorem insertLoop_exhausted (owner : IndexOwner) (d : Device) (draws : List Draw)
    (allCollide : ∀ draw ∈ draws, d.indexTable.any (·.index == draw.value) = true)
    (turns : List Nat) (enough : draws.length < turns.length)
    (w : World) (device : w.k.wg = some d)
    (records : w.hidden = some (draws.map Draw.record)) :
    (insertLoop owner turns).run w = .error missingIndexDraw := by
  induction draws generalizing turns w with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      simp only [List.map_nil] at records
      simp only [insertLoop, List.forIn_cons, StateT.run_bind,
        insertStep_empty owner turn (none, ()) w records]
      rfl
  | cons draw draws ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      obtain ⟨result, middle, firstRun, value, nextDevice, nextRecords⟩ :=
        insertStep_collision owner turn (none, ()) d draw (draws.map Draw.record)
          (allCollide draw (by simp)) w ⟨device, records⟩
      subst result
      have restCollide : ∀ r ∈ draws, d.indexTable.any (·.index == r.value) = true := by
        intro r member
        exact allCollide r (by simp [member])
      have restEnough : draws.length < turns.length := by simpa using enough
      simp only [insertLoop, List.forIn_cons, StateT.run_bind, firstRun]
      exact ih restCollide turns restEnough middle nextDevice nextRecords

theorem indexInsert_exhausted (owner : IndexOwner) (d : Device) (draws : List Draw)
    (allCollide : ∀ draw ∈ draws,
      (removeOwner owner d.indexTable).any (·.index == draw.value) = true)
    (w : World) (device : w.k.wg = some d)
    (records : w.hidden = some (draws.map Draw.record)) :
    (indexInsert owner).run w = .error missingIndexDraw := by
  obtain ⟨u, middle, unhash, nextDevice, nextRecords⟩ :=
    unhash_records_returns .idxInsertHashed owner d (some (draws.map Draw.record)) w ⟨device, records⟩
  have budget : recordBudget.run middle = .ok ((draws.map Draw.record).length + 1, middle) := by
    simp [recordBudget, StateT.run, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.pure, StateT.get, Except.bind, Except.pure, nextRecords]
  have loop : (forIn ([:(draws.map Draw.record).length + 1] : Std.Legacy.Range)
      (none, ()) (insertStep owner)).run middle = .error missingIndexDraw := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    apply insertLoop_exhausted owner { d with indexTable := removeOwner owner d.indexTable }
      draws allCollide _ _ middle nextDevice nextRecords
    simp
  rw [indexInsert_source, StateT.run_bind, unhash]
  change ((do
    let count ← recordBudget
    let state ← forIn ([:count] : Std.Legacy.Range) (none, ()) (insertStep owner)
    insertFinish state).run middle) = _
  rw [StateT.run_bind, budget]
  change ((do
    let state ← forIn ([:(draws.map Draw.record).length + 1] : Std.Legacy.Range) (none, ()) (insertStep owner)
    insertFinish state).run middle) = _
  rw [StateT.run_bind, loop]
  rfl

end Leanux.Proofs.WG.Index
