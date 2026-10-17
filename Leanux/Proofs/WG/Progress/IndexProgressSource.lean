import Leanux.Proofs.WG.Progress.IndexProgressModel
import Leanux.Proofs.WG.Index.DrawRecords

/-! Exact original hidden-read and insertion-loop correspondence. Component
helpers run on the actual index table and Ambient; the whole insertion uses the
original guarded liftIndex and retains the selected Device and record suffix.
Every supplied record list remains in scope, including malformed input and
passive prefixes. Errors carry no final state. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Index Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem hidden_index_arbitrary (w : Ambient) (records : List HiddenRecord)
    (present : w.hidden = some records) :
    (AmbientM.hidden .indexDraw).run w =
      match resolveIndexInput records with
      | .error error => .error error
      | .ok (bytes, rest) => .ok (bytes, {w with hidden := some rest}) := by
  cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil =>
    simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveIndexInput, stripped]
    rfl
  | cons record rest =>
    simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveIndexInput, stripped]
    split <;> (try rfl)
    split <;> rfl

theorem hiddenInput_returns (d : Device) (records : List HiddenRecord)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (resolution : resolveIndexInput records = .ok (bytes, rest)) (g : WGWorld) :
    Config.Product.Returns ((hidden .indexDraw : WG.M (List UInt8)).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some records)
      (fun (out, current) ambient => out = bytes ∧ current.dev = some d ∧ ambient.hidden = some rest) := by
  intro ambient pre
  refine ⟨(bytes, g), {ambient with hidden := some rest}, ?_, rfl, pre.1, rfl⟩
  change ((AmbientM.hidden .indexDraw).run ambient).map
    (fun (value, after) => ((value, g), after)) = _
  rw [hidden_index_arbitrary ambient records pre.2, resolution]
  rfl

theorem insertStep_input (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (table : List IndexEntry) (records : List HiddenRecord) (bytes : List UInt8) (rest : List HiddenRecord)
    (resolution : resolveIndexInput records = .ok (bytes, rest)) :
    Config.Product.Returns ((insertStep owner turn state).run table)
      (fun ambient => ambient.hidden = some records)
      (fun (result, current) ambient =>
        let index := bytes.foldr (fun b acc => acc * 256 + b.toNat) 0
        if table.any (·.index == index) then
          result = .yield (none, ()) ∧ current = table ∧ ambient.hidden = some rest
        else result = .done (some index, ()) ∧
          current = {index, owner} :: table ∧ ambient.hidden = some rest) := by
  intro ambient present
  let index := bytes.foldr (fun b acc => acc * 256 + b.toNat) 0
  let afterDraw := {ambient with hidden := some rest}
  have drawRun : ((hidden .indexDraw : IndexM (List UInt8)).run table).run ambient =
      .ok ((bytes, table), afterDraw) := by
    change ((AmbientM.hidden .indexDraw).run ambient).map
      (fun (value, after) => ((value, table), after)) = _
    rw [hidden_index_arbitrary ambient records present, resolution]
    rfl
  have hb (walk collide : Decision) (before : Ambient) (hidden : before.hidden = some rest) :
      ∃ after, ((bucketHas walk collide index).run table).run before =
        .ok ((table.any (·.index == index), table), after) ∧ after.hidden = some rest := by
    obtain ⟨⟨found, current⟩, after, run, value, same, tail⟩ :=
      bucketWalk_records_returns walk collide index (bucket index table) table (some rest) before hidden
    subst current
    have foundValue : found = table.any (·.index == index) := by simpa [bucket_any] using value
    rw [foundValue] at run
    refine ⟨after, ?_, tail⟩
    rw [bucketHas_source]
    simpa [indexBucket, bucket] using run
  obtain ⟨middle, firstRun, firstHidden⟩ := hb .idxInsWalk1 .idxInsCollide1 afterDraw rfl
  cases collision : table.any (·.index == index) with
  | true =>
    rw [collision] at firstRun
    refine ⟨(.yield (none, ()), table), middle, ?_, ?_⟩
    · simp only [insertStep, StateT.run_bind]
      rw [drawRun]
      change (((bucketHas .idxInsWalk1 .idxInsCollide1 index).run table).run afterDraw >>= _) = _
      rw [firstRun]
      rfl
    · change (if table.any (·.index == index) then _ else _)
      rw [collision]
      exact ⟨rfl, rfl, firstHidden⟩
  | false =>
    obtain ⟨after, secondRun, tail⟩ := hb .idxInsWalk2 .idxInsCollide2 middle firstHidden
    rw [collision] at firstRun secondRun
    refine ⟨(.done (some index, ()), {index, owner} :: table), after, ?_, ?_⟩
    · simp only [insertStep, StateT.run_bind]
      rw [drawRun]
      change (((bucketHas .idxInsWalk1 .idxInsCollide1 index).run table).run afterDraw >>= _) = _
      rw [firstRun]
      change (((bucketHas .idxInsWalk2 .idxInsCollide2 index).run table).run middle >>= _) = _
      rw [secondRun]
      rfl
    · change (if table.any (·.index == index) then _ else _)
      rw [collision]
      exact ⟨rfl, rfl, tail⟩

theorem insertStep_input_error (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (table : List IndexEntry) (ambient : Ambient) (records : List HiddenRecord) (error : Stop)
    (present : ambient.hidden = some records)
    (resolution : resolveIndexInput records = .error error) :
    ((insertStep owner turn state).run table).run ambient = .error error := by
  have first : ((hidden .indexDraw : IndexM (List UInt8)).run table).run ambient =
      .error error := by
    change ((AmbientM.hidden .indexDraw).run ambient).map
      (fun (value, after) => ((value, table), after)) = _
    rw [hidden_index_arbitrary ambient records present, resolution]
    rfl
  simp only [insertStep, StateT.run_bind]
  rw [first]
  rfl

theorem insertLoop_input (owner : IndexOwner) (table : List IndexEntry) (turns : List Nat)
    (records : List HiddenRecord) (enough : records.length + 1 ≤ turns.length)
    (ambient : Ambient) (present : ambient.hidden = some records) :
    match resolveIndexSearch table records with
    | .error error => ((insertLoop owner turns).run table).run ambient = .error error
    | .ok (index, rest) => ∃ final after,
      ((insertLoop owner turns).run table).run ambient = .ok (((some index, ()), final), after) ∧
      final = {index, owner} :: table ∧ after.hidden = some rest := by
  induction turns generalizing records ambient with
  | nil => simp at enough
  | cons turn turns ih =>
    rw [resolveIndexSearch]
    cases resolution : resolveIndexInput records with
    | error error =>
      dsimp only
      have first := insertStep_input_error owner turn (none, ()) table ambient records error present resolution
      simp only [insertLoop, List.forIn_cons, StateT.run_bind]
      rw [first]
      rfl
    | ok pair =>
      rcases pair with ⟨bytes, rest⟩
      dsimp only
      obtain ⟨⟨step, middle⟩, next, first, post⟩ :=
        insertStep_input owner turn (none, ()) table records bytes rest resolution ambient present
      dsimp only at post
      by_cases collision : table.any (·.index == bytes.foldr (fun b acc => acc * 256 + b.toNat) 0) = true
      · rw [ite_eq_left collision] at post ⊢
        obtain ⟨rfl, middleTable, middleHidden⟩ := post
        subst middle
        have smaller := (resolveIndexInput_suffix records bytes rest resolution).2
        have bound : rest.length + 1 ≤ turns.length := by simp only [List.length_cons] at enough; omega
        have nextRun := ih rest bound next middleHidden
        cases outcome : resolveIndexSearch table rest with
        | error error =>
          simp only [outcome] at nextRun ⊢
          simp only [insertLoop, List.forIn_cons, StateT.run_bind]
          rw [first]
          exact nextRun
        | ok pair =>
          rcases pair with ⟨index, tail⟩
          simp only [outcome] at nextRun ⊢
          obtain ⟨final, after, run, finalTable, finalHidden⟩ := nextRun
          refine ⟨final, after, ?_, finalTable, finalHidden⟩
          simp only [insertLoop, List.forIn_cons, StateT.run_bind]
          rw [first]
          exact run
      · rw [ite_eq_right collision] at post ⊢
        obtain ⟨rfl, middleTable, middleHidden⟩ := post
        refine ⟨middle, next, ?_, middleTable, middleHidden⟩
        simp only [insertLoop, List.forIn_cons, StateT.run_bind]
        rw [first]
        rfl

theorem indexInsert_input (owner : IndexOwner) (d : Device) (records : List HiddenRecord)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) (present : ambient.hidden = some records) :
    match resolveIndexSearch (removeOwner owner d.indexTable) records with
    | .error error => ((liftIndex (indexInsert owner)).run g).run ambient = .error error
    | .ok (index, rest) => ∃ final after,
      ((liftIndex (indexInsert owner)).run g).run ambient = .ok ((index, final), after) ∧
      final.dev = some {d with indexTable := {index, owner} :: removeOwner owner d.indexTable} ∧
      after.hidden = some rest := by
  let removed := removeOwner owner d.indexTable
  let start := {ambient with steps := ambient.steps.push {
    decision := Decision.idxInsertHashed, outcome := d.indexTable.any (·.owner == owner),
    netRx := ambient.netRxSection}}
  have unhashRun : ((unhashEntry .idxInsertHashed (·.owner == owner)).run d.indexTable).run ambient =
      .ok (((), removed), start) := by
    simp [unhashEntry, removed, removeOwner, start]
    rfl
  have budgetRun : ((recordBudget : IndexM Nat).run removed).run start =
      .ok ((records.length + 1, removed), start) := by
    simp [recordBudget, AmbientM.recordBudget, start, present]
    rfl
  have loop := insertLoop_input owner removed (List.range' 0 (records.length + 1)) records
    (by simp) start present
  have rangeEq :
      (forIn ([:records.length + 1] : Std.Legacy.Range) (none, ()) (insertStep owner)) =
        insertLoop owner (List.range' 0 (records.length + 1)) := by
    simp [Std.Legacy.Range.forIn_eq_forIn_range', insertLoop]
  cases outcome : resolveIndexSearch (removeOwner owner d.indexTable) records with
  | error error =>
    simp only [removed, outcome] at loop ⊢
    have native : ((indexInsert owner).run d.indexTable).run ambient = .error error := by
      rw [indexInsert_source]
      simp only [StateT.run_bind]
      rw [unhashRun]
      simp only [bind, Except.bind]
      rw [budgetRun]
      dsimp only
      rw [rangeEq, loop]
    rw [liftIndex_run_variant, device]
    simp only [native, Except.map]
  | ok pair =>
    rcases pair with ⟨index, rest⟩
    simp only [removed, outcome] at loop ⊢
    obtain ⟨final, after, run, finalTable, finalHidden⟩ := loop
    subst final
    have native : ((indexInsert owner).run d.indexTable).run ambient =
        .ok ((index, {index, owner} :: removed), after) := by
      rw [indexInsert_source]
      simp only [StateT.run_bind]
      rw [unhashRun]
      simp only [bind, Except.bind]
      rw [budgetRun]
      dsimp only
      rw [rangeEq, run]
      rfl
    refine ⟨{g with dev := some {d with indexTable := {index, owner} :: removed}},
      after, ?_, rfl, finalHidden⟩
    rw [liftIndex_run_variant, device]
    simp only [native, Except.map]

end Leanux.Proofs.WG.Progress
