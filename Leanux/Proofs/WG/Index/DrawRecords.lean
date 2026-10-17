import Leanux.Proofs.WG.Index.DrawRecordSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem insertStep_collision (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (d : Device) (draw : Draw) (rest : List HiddenRecord)
    (collision : d.indexTable.any (·.index == draw.value) = true) :
    Returns (insertStep owner turn state)
      (fun w => w.k.wg = some d ∧ w.hidden = some (draw.record :: rest))
      (fun result w => result = .yield (none, ()) ∧
        w.k.wg = some d ∧ w.hidden = some rest) := by
  have hh := (returns_iff _ _ _).mp (hiddenIndex_returns draw rest d)
  have hb := fun walk collide index => (returns_iff _ _ _).mp
    (bucketHas_records_returns walk collide index d (some rest))
  rw [returns_iff]
  mvcgen [insertStep, hh, hb]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [Draw.value]
  all_goals subst_vars
  all_goals mvcgen [hb]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [Draw.value]

theorem insertStep_fresh (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (d : Device) (draw : Draw) (rest : List HiddenRecord)
    (fresh : d.indexTable.any (·.index == draw.value) = false) :
    Returns (insertStep owner turn state)
      (fun w => w.k.wg = some d ∧ w.hidden = some (draw.record :: rest))
      (fun result w => result = .done (some draw.value, ()) ∧
        w.k.wg = some { d with indexTable := { index := draw.value, owner } :: d.indexTable } ∧
        w.hidden = some rest) := by
  have hh := (returns_iff _ _ _).mp (hiddenIndex_returns draw rest d)
  have hb := fun walk collide index => (returns_iff _ _ _).mp
    (bucketHas_records_returns walk collide index d (some rest))
  rw [returns_iff]
  mvcgen [insertStep, hh, hb, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [Draw.value]
  all_goals subst_vars
  all_goals try solve | grind only
  all_goals mvcgen [hb, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [Draw.value]

/-- A contiguous collision prefix followed by the first fresh recorded draw. -/
def drawStream (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord) :
    List HiddenRecord := collisions.map Draw.record ++ fresh.record :: rest

theorem insertLoop_records (owner : IndexOwner) (d : Device)
    (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions, d.indexTable.any (·.index == draw.value) = true)
    (isFresh : d.indexTable.any (·.index == fresh.value) = false)
    (turns : List Nat) (enough : collisions.length + 1 ≤ turns.length) :
    Returns (insertLoop owner turns)
      (fun w => w.k.wg = some d ∧ w.hidden = some (drawStream collisions fresh rest))
      (fun result w => result = (some fresh.value, ()) ∧
        w.k.wg = some { d with indexTable := { index := fresh.value, owner } :: d.indexTable } ∧
        w.hidden = some rest) := by
  induction collisions generalizing turns with
  | nil =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      intro w pre
      obtain ⟨result, final, run, value, device, records⟩ :=
        insertStep_fresh owner turn (none, ()) d fresh rest isFresh w pre
      subst result
      refine ⟨(some fresh.value, ()), final, ?_, rfl, device, records⟩
      simp only [insertLoop, List.forIn_cons, StateT.run_bind]
      rw [run]
      rfl
  | cons draw draws ih =>
    cases turns with
    | nil => simp at enough
    | cons turn turns =>
      intro w pre
      have firstCollides := allCollide draw (by simp)
      have remainingCollide : ∀ r ∈ draws, d.indexTable.any (·.index == r.value) = true := by
        intro r member
        exact allCollide r (by simp [member])
      have remainingEnough : draws.length + 1 ≤ turns.length := by simpa using enough
      obtain ⟨result, middle, firstRun, value, device, records⟩ :=
        insertStep_collision owner turn (none, ()) d draw (drawStream draws fresh rest)
          firstCollides w pre
      subst result
      obtain ⟨result, final, restRun, post⟩ :=
        ih remainingCollide turns remainingEnough middle ⟨device, records⟩
      refine ⟨result, final, ?_, post⟩
      simp only [insertLoop, List.forIn_cons, StateT.run_bind]
      rw [firstRun]
      exact restRun

theorem insertRange_records (owner : IndexOwner) (d : Device)
    (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions, d.indexTable.any (·.index == draw.value) = true)
    (isFresh : d.indexTable.any (·.index == fresh.value) = false)
    (budget : Nat) (enough : collisions.length + 1 ≤ budget) :
    Returns (forIn ([:budget] : Std.Legacy.Range) (none, ()) (insertStep owner))
      (fun w => w.k.wg = some d ∧ w.hidden = some (drawStream collisions fresh rest))
      (fun result w => result = (some fresh.value, ()) ∧
        w.k.wg = some { d with indexTable := { index := fresh.value, owner } :: d.indexTable } ∧
        w.hidden = some rest) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply insertLoop_records owner d collisions fresh rest allCollide isFresh
  simpa using enough

/-- The record-derived budget suffices for every finite contiguous collision
prefix followed by a fresh draw; the unused suffix is preserved exactly. -/
theorem indexInsert_records (owner : IndexOwner) (d : Device)
    (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (removeOwner owner d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (removeOwner owner d.indexTable).any (·.index == fresh.value) = false) :
    Returns (indexInsert owner)
      (fun w => w.k.wg = some d ∧ w.hidden = some (drawStream collisions fresh rest))
      (fun result w => result = fresh.value ∧
        w.k.wg = some { d with indexTable :=
          { index := fresh.value, owner } :: removeOwner owner d.indexTable } ∧
        w.hidden = some rest) := by
  let removed := { d with indexTable := removeOwner owner d.indexTable }
  let records := drawStream collisions fresh rest
  have hb : Returns recordBudget
      (fun w => w.k.wg = some removed ∧ w.hidden = some records)
      (fun budget w => budget = records.length + 1 ∧
        w.k.wg = some removed ∧ w.hidden = some records) := by
    rw [returns_iff]
    mvcgen [recordBudget]
    all_goals simp_all
  have enough : collisions.length + 1 ≤ records.length + 1 := by
    simp [records, drawStream]
  rw [indexInsert_source]
  refine returns_bind _ _ (unhash_records_returns .idxInsertHashed owner d (some records)) ?_
  intro u
  refine returns_bind _ _ hb ?_
  intro budget w pre
  obtain ⟨eq, device, hidden⟩ := pre
  subst budget
  have hr := insertRange_records owner removed collisions fresh rest allCollide isFresh
    (records.length + 1) enough
  have hf : ∀ state, Returns (insertFinish state)
      (fun w => state = (some fresh.value, ()) ∧
        w.k.wg = some { removed with indexTable := { index := fresh.value, owner } :: removed.indexTable } ∧
        w.hidden = some rest)
      (fun result w => result = fresh.value ∧
        w.k.wg = some { d with indexTable :=
          { index := fresh.value, owner } :: removeOwner owner d.indexTable } ∧
        w.hidden = some rest) := by
    intro state v h
    obtain ⟨eq, hd, hh⟩ := h
    subst state
    exact ⟨fresh.value, v, rfl, rfl, hd, hh⟩
  exact returns_bind _ _ hr hf w ⟨device, hidden⟩

end Leanux.Proofs.WG.Index
