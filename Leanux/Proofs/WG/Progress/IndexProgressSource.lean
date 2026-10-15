import Leanux.Proofs.WG.Progress.IndexProgressModel
import Leanux.Proofs.WG.Index.DrawRecords

/-! Exact original hidden-read and insertion-loop correspondence. The selected
device and remaining records are retained on success; errors have no final
state. No structural frame layer is introduced. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Index Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem hidden_index_arbitrary (w : World) (records : List HiddenRecord)
    (present : w.hidden = some records) :
    (hidden .indexDraw).run w =
      match resolveIndexInput records with
      | .error error => .error error
      | .ok (bytes, rest) => .ok (bytes, {w with hidden := some rest}) := by
  cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil =>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveIndexInput, stripped]
    rfl
  | cons record rest =>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveIndexInput, stripped]
    split <;> (try rfl)
    split <;> rfl

theorem hiddenInput_returns (d : Device) (records : List HiddenRecord)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (resolution : resolveIndexInput records = .ok (bytes, rest)) :
    Returns (hidden .indexDraw)
      (fun w => w.k.wg = some d ∧ w.hidden = some records)
      (fun out w => out = bytes ∧ w.k.wg = some d ∧ w.hidden = some rest) := by
  intro w pre
  refine ⟨bytes, {w with hidden := some rest}, ?_, rfl, pre.1, rfl⟩
  rw [hidden_index_arbitrary w records pre.2, resolution]

theorem insertStep_input (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (d : Device) (records : List HiddenRecord) (bytes : List UInt8) (rest : List HiddenRecord)
    (resolution : resolveIndexInput records = .ok (bytes, rest)) :
    Returns (insertStep owner turn state)
      (fun w => w.k.wg = some d ∧ w.hidden = some records)
      (fun result w =>
        let index := bytes.foldr (fun b acc => acc * 256 + b.toNat) 0
        if d.indexTable.any (·.index == index) then
          result = .yield (none, ()) ∧ w.k.wg = some d ∧ w.hidden = some rest
        else result = .done (some index, ()) ∧
          w.k.wg = some {d with indexTable := {index, owner} :: d.indexTable} ∧ w.hidden = some rest) := by
  have hh := (returns_iff _ _ _).mp (hiddenInput_returns d records bytes rest resolution)
  have hb := fun walk collide index => (returns_iff _ _ _).mp
    (bucketHas_records_returns walk collide index d (some rest))
  rw [returns_iff]
  mvcgen [insertStep, hh, hb, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals try solve | grind only
  all_goals mvcgen [hb, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all


theorem insertStep_input_error (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (w : World) (records : List HiddenRecord) (error : Stop)
    (present : w.hidden = some records)
    (resolution : resolveIndexInput records = .error error) :
    (insertStep owner turn state).run w = .error error := by
  change ((hidden .indexDraw).run w >>= _) = _
  rw [hidden_index_arbitrary w records present, resolution]
  rfl

theorem insertLoop_input (owner : IndexOwner) (d : Device) (turns : List Nat)
    (records : List HiddenRecord) (enough : records.length + 1 ≤ turns.length)
    (w : World) (device : w.k.wg = some d) (present : w.hidden = some records) :
    match resolveIndexSearch d.indexTable records with
    | .error error => (insertLoop owner turns).run w = .error error
    | .ok (index, rest) => ∃ final,
      (insertLoop owner turns).run w = .ok ((some index, ()), final) ∧
      final.k.wg = some {d with indexTable := {index, owner} :: d.indexTable} ∧
      final.hidden = some rest := by
  induction turns generalizing records w with
  | nil => simp at enough
  | cons turn turns ih =>
    rw [resolveIndexSearch]
    cases resolution : resolveIndexInput records with
    | error error =>
      dsimp only
      have first := insertStep_input_error owner turn (none, ()) w records error present resolution
      simp only [insertLoop, List.forIn_cons, StateT.run_bind]
      rw [first]
      rfl
    | ok pair =>
      rcases pair with ⟨bytes, rest⟩
      dsimp only
      obtain ⟨step, middle, first, post⟩ :=
        insertStep_input owner turn (none, ()) d records bytes rest resolution w ⟨device, present⟩
      by_cases collision : d.indexTable.any (·.index == bytes.foldr (fun b acc => acc * 256 + b.toNat) 0) = true
      · rw [ite_eq_left collision] at post ⊢
        obtain ⟨rfl, middleDevice, middleHidden⟩ := post
        have smaller := (resolveIndexInput_suffix records bytes rest resolution).2
        have bound : rest.length + 1 ≤ turns.length := by simp only [List.length_cons] at enough; omega
        have next := ih rest bound middle middleDevice middleHidden
        cases outcome : resolveIndexSearch d.indexTable rest with
        | error error =>
          simp only [outcome] at next ⊢
          simp only [insertLoop, List.forIn_cons, StateT.run_bind]
          rw [first]
          exact next
        | ok pair =>
          rcases pair with ⟨index, tail⟩
          simp only [outcome] at next ⊢
          obtain ⟨final, run, finalDevice, finalHidden⟩ := next
          refine ⟨final, ?_, finalDevice, finalHidden⟩
          simp only [insertLoop, List.forIn_cons, StateT.run_bind]
          rw [first]
          exact run
      · rw [ite_eq_right collision] at post ⊢
        obtain ⟨rfl, middleDevice, middleHidden⟩ := post
        refine ⟨middle, ?_, middleDevice, middleHidden⟩
        simp only [insertLoop, List.forIn_cons, StateT.run_bind]
        rw [first]
        rfl


theorem indexInsert_input (owner : IndexOwner) (d : Device) (records : List HiddenRecord)
    (w : World) (device : w.k.wg = some d) (present : w.hidden = some records) :
    match resolveIndexSearch (removeOwner owner d.indexTable) records with
    | .error error => (indexInsert owner).run w = .error error
    | .ok (index, rest) => ∃ final,
      (indexInsert owner).run w = .ok (index, final) ∧
      final.k.wg = some {d with indexTable := {index, owner} :: removeOwner owner d.indexTable} ∧
      final.hidden = some rest := by
  let removed := {d with indexTable := removeOwner owner d.indexTable}
  obtain ⟨u, middle, unhashRun, middleDevice, middleHidden⟩ :=
    unhash_records_returns .idxInsertHashed owner d (some records) w ⟨device, present⟩
  have budgetRun : recordBudget.run middle = .ok (records.length + 1, middle) := by
    change (Except.ok ((match middle.hidden with | some rs => rs.length + 1 | none => DOMAIN_FILTER_TURNS), middle) : Except Stop (Nat × World)) = _
    rw [middleHidden]
  have loop := insertLoop_input owner removed (List.range' 0 (records.length + 1)) records
    (by simp) middle middleDevice middleHidden
  have rangeEq :
      (forIn ([:records.length + 1] : Std.Legacy.Range) (none, ()) (insertStep owner)) =
        insertLoop owner (List.range' 0 (records.length + 1)) := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', insertLoop]
  cases outcome : resolveIndexSearch (removeOwner owner d.indexTable) records with
  | error error =>
    simp only [removed, outcome] at loop ⊢
    rw [indexInsert_source]
    simp only [StateT.run_bind]
    rw [unhashRun]
    simp only [bind, Except.bind, budgetRun]
    rw [rangeEq, loop]
  | ok pair =>
    rcases pair with ⟨index, rest⟩
    simp only [removed, outcome] at loop ⊢
    obtain ⟨final, run, finalDevice, finalHidden⟩ := loop
    refine ⟨final, ?_, finalDevice, finalHidden⟩
    rw [indexInsert_source]
    simp only [StateT.run_bind]
    rw [unhashRun]
    simp only [bind, Except.bind, budgetRun]
    rw [rangeEq, run]
    rfl



end Leanux.Proofs.WG.Progress
