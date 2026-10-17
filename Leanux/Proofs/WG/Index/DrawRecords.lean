import Leanux.Proofs.WG.Index.DrawRecordSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem insertStep_collision (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (table : List IndexEntry) (draw : Draw) (rest : List HiddenRecord)
    (collision : table.any (·.index == draw.value) = true) :
    Config.Product.Returns ((insertStep owner turn state).run table)
      (fun ambient => ambient.hidden = some (draw.record :: rest))
      (fun (result, current) ambient =>
        result = .yield (none, ()) ∧ current = table ∧ ambient.hidden = some rest) := by
  intro ambient records
  let afterDraw := {ambient with hidden := some rest}
  have drawRun : ((hidden .indexDraw : IndexM (List UInt8)).run table).run ambient =
      .ok ((draw.bytes, table), afterDraw) := by
    change ((AmbientM.hidden .indexDraw).run ambient).map
      (fun (bytes, after) => ((bytes, table), after)) = _
    rw [hiddenIndex_run ambient draw rest records]
    rfl
  obtain ⟨⟨found, current⟩, after, walkRun, first, same, tail⟩ :=
    bucketWalk_records_returns .idxInsWalk1 .idxInsCollide1 draw.value
      (bucket draw.value table) table (some rest) afterDraw rfl
  subst current
  have isTrue : found = true := by simpa [bucket_any, collision] using first
  rw [isTrue] at walkRun
  have firstRun : ((bucketHas .idxInsWalk1 .idxInsCollide1 draw.value).run table).run afterDraw =
      .ok ((true, table), after) := by
    rw [bucketHas_source]
    simpa [indexBucket, bucket] using walkRun
  refine ⟨(.yield (none, ()), table), after, ?_, rfl, rfl, tail⟩
  simp only [insertStep, StateT.run_bind]
  rw [drawRun]
  change (((bucketHas .idxInsWalk1 .idxInsCollide1 draw.value).run table).run afterDraw >>= _) = _
  rw [firstRun]
  rfl

theorem insertStep_fresh (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (table : List IndexEntry) (draw : Draw) (rest : List HiddenRecord)
    (fresh : table.any (·.index == draw.value) = false) :
    Config.Product.Returns ((insertStep owner turn state).run table)
      (fun ambient => ambient.hidden = some (draw.record :: rest))
      (fun (result, current) ambient =>
        result = .done (some draw.value, ()) ∧
        current = {index := draw.value, owner} :: table ∧ ambient.hidden = some rest) := by
  intro ambient records
  let afterDraw := {ambient with hidden := some rest}
  have drawRun : ((hidden .indexDraw : IndexM (List UInt8)).run table).run ambient =
      .ok ((draw.bytes, table), afterDraw) := by
    change ((AmbientM.hidden .indexDraw).run ambient).map
      (fun (bytes, after) => ((bytes, table), after)) = _
    rw [hiddenIndex_run ambient draw rest records]
    rfl
  have hb (walk collide : Decision) (before : Ambient) (hidden : before.hidden = some rest) :
      ∃ after, ((bucketHas walk collide draw.value).run table).run before =
        .ok ((false, table), after) ∧ after.hidden = some rest := by
    obtain ⟨⟨found, current⟩, after, walkRun, first, same, tail⟩ :=
      bucketWalk_records_returns walk collide draw.value
        (bucket draw.value table) table (some rest) before hidden
    subst current
    have isFalse : found = false := by simpa [bucket_any, fresh] using first
    rw [isFalse] at walkRun
    refine ⟨after, ?_, tail⟩
    rw [bucketHas_source]
    simpa [indexBucket, bucket] using walkRun
  obtain ⟨middle, firstRun, hidden⟩ := hb .idxInsWalk1 .idxInsCollide1 afterDraw rfl
  obtain ⟨after, secondRun, tail⟩ := hb .idxInsWalk2 .idxInsCollide2 middle hidden
  refine ⟨(.done (some draw.value, ()), {index := draw.value, owner} :: table),
    after, ?_, rfl, rfl, tail⟩
  simp only [insertStep, StateT.run_bind]
  rw [drawRun]
  change (((bucketHas .idxInsWalk1 .idxInsCollide1 draw.value).run table).run afterDraw >>= _) = _
  rw [firstRun]
  change (((bucketHas .idxInsWalk2 .idxInsCollide2 draw.value).run table).run middle >>= _) = _
  rw [secondRun]
  rfl


/-- A contiguous collision prefix followed by the first fresh recorded draw. -/
def drawStream (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord) :
    List HiddenRecord := collisions.map Draw.record ++ fresh.record :: rest

theorem insertLoop_records (owner : IndexOwner) (table : List IndexEntry)
    (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions, table.any (·.index == draw.value) = true)
    (isFresh : table.any (·.index == fresh.value) = false)
    (turns : List Nat) (enough : collisions.length + 1 ≤ turns.length) :
    Config.Product.Returns ((insertLoop owner turns).run table)
      (fun ambient => ambient.hidden = some (drawStream collisions fresh rest))
      (fun (result, current) ambient => result = (some fresh.value, ()) ∧
        current = {index := fresh.value, owner} :: table ∧ ambient.hidden = some rest) := by
  induction collisions generalizing turns with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      intro ambient pre
      obtain ⟨⟨result, final⟩, after, run, value, state, records⟩ :=
        insertStep_fresh owner turn (none, ()) table fresh rest isFresh ambient pre
      subst result
      refine ⟨((some fresh.value, ()), final), after, ?_, rfl, state, records⟩
      simp only [insertLoop, List.forIn_cons, StateT.run_bind]
      rw [run]
      rfl
  | cons draw draws ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      intro ambient pre
      have firstCollides := allCollide draw (by simp)
      have remainingCollide : ∀ r ∈ draws, table.any (·.index == r.value) = true := by
        intro r member
        exact allCollide r (by simp [member])
      have remainingEnough : draws.length + 1 ≤ turns.length := by simpa using enough
      obtain ⟨⟨result, middle⟩, next, firstRun, value, state, records⟩ :=
        insertStep_collision owner turn (none, ()) table draw (drawStream draws fresh rest)
          firstCollides ambient pre
      subst result
      subst middle
      obtain ⟨result, after, restRun, post⟩ :=
        ih remainingCollide turns remainingEnough next records
      refine ⟨result, after, ?_, post⟩
      simp only [insertLoop, List.forIn_cons, StateT.run_bind]
      rw [firstRun]
      exact restRun

theorem insertRange_records (owner : IndexOwner) (table : List IndexEntry)
    (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions, table.any (·.index == draw.value) = true)
    (isFresh : table.any (·.index == fresh.value) = false)
    (budget : Nat) (enough : collisions.length + 1 ≤ budget) :
    Config.Product.Returns
      ((forIn ([:budget] : Std.Legacy.Range) (none, ()) (insertStep owner)).run table)
      (fun ambient => ambient.hidden = some (drawStream collisions fresh rest))
      (fun (result, current) ambient => result = (some fresh.value, ()) ∧
        current = {index := fresh.value, owner} :: table ∧ ambient.hidden = some rest) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply insertLoop_records owner table collisions fresh rest allCollide isFresh
  simpa using enough

/-- The record-derived budget suffices for every finite contiguous collision
prefix followed by a fresh draw; the unused suffix is preserved exactly. -/
theorem indexInsert_records (owner : IndexOwner) (d : Device)
    (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (removeOwner owner d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (removeOwner owner d.indexTable).any (·.index == fresh.value) = false)
    (g : WGWorld) :
    Config.Product.Returns ((liftIndex (indexInsert owner)).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some (drawStream collisions fresh rest))
      (fun (result, current) ambient => result = fresh.value ∧
        current.dev = some {d with indexTable :=
          {index := fresh.value, owner} :: removeOwner owner d.indexTable} ∧
        ambient.hidden = some rest) := by
  intro ambient pre
  let removed := removeOwner owner d.indexTable
  let records := drawStream collisions fresh rest
  let start := {ambient with steps := ambient.steps.push {
    decision := Decision.idxInsertHashed, outcome := d.indexTable.any (·.owner == owner),
    netRx := ambient.netRxSection}}
  have enough : collisions.length + 1 ≤ records.length + 1 := by
    simp [records, drawStream]
  obtain ⟨⟨result, final⟩, after, rangeRun, value, state, tail⟩ :=
    insertRange_records owner removed collisions fresh rest allCollide isFresh
      (records.length + 1) enough start pre.2
  subst result
  subst final
  have unhashRun : ((unhashEntry .idxInsertHashed (·.owner == owner)).run d.indexTable).run ambient =
      .ok (((), removed), start) := by
    simp [unhashEntry, removed, removeOwner, start]
    rfl
  have budgetRun : ((recordBudget : IndexM Nat).run removed).run start =
      .ok ((records.length + 1, removed), start) := by
    simp [recordBudget, AmbientM.recordBudget, start, pre.2, records]
    rfl
  have native : ((indexInsert owner).run d.indexTable).run ambient =
      .ok ((fresh.value, {index := fresh.value, owner} :: removed), after) := by
    rw [indexInsert_source]
    simp only [StateT.run_bind]
    rw [unhashRun]
    simp only [bind, Except.bind]
    rw [budgetRun]
    dsimp only
    rw [rangeRun]
    rfl
  refine ⟨(fresh.value, {g with dev := some {d with indexTable :=
    {index := fresh.value, owner} :: removed}}), after, ?_, rfl, rfl, tail⟩
  rw [liftIndex_run_variant, pre.1]
  simp only [native, Except.map]

end Leanux.Proofs.WG.Index
