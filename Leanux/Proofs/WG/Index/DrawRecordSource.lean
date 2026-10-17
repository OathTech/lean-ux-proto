import Leanux.Proofs.WG.Index.Insert

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Exactly the four payload bytes recorded by get_random_bytes for an index. -/
structure Draw where
  a : UInt8
  b : UInt8
  c : UInt8
  d : UInt8
  deriving Repr

def Draw.bytes (draw : Draw) : List UInt8 := [draw.a, draw.b, draw.c, draw.d]
def Draw.value (draw : Draw) : Nat := draw.bytes.foldr (fun b acc => acc * 256 + b.toNat) 0
def Draw.record (draw : Draw) : HiddenRecord :=
  { site := HiddenSite.indexDraw.info.id, bytes := draw.bytes ++ [0, 0, 0, 0] }

/-- Consume the nonambient index record on the actual Ambient state; every
other Ambient field remains exact. The enclosing native state is untouched by
the canonical lift. -/
theorem hiddenIndex_run (ambient : Ambient) (draw : Draw) (rest : List HiddenRecord)
    (records : ambient.hidden = some (draw.record :: rest)) :
    (AmbientM.hidden .indexDraw).run ambient =
      .ok (draw.bytes, {ambient with hidden := some rest}) := by
  have passive : HiddenSite.passive 4 = false := by decide
  simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    records, Draw.record, Draw.bytes, HiddenSite.info, passive, Worker.sectionId, Worker.index,
    Except.pure, Except.bind]

theorem bucketWalk_records_returns (walk collide : Decision) (index : Nat)
    (entries table : List IndexEntry) (records : Option (List HiddenRecord)) :
    Config.Product.Returns ((bucketWalk walk collide index entries).run table)
      (fun ambient => ambient.hidden = records)
      (fun (result, current) ambient =>
        result = entries.any (·.index == index) ∧ current = table ∧ ambient.hidden = records) := by
  induction entries with
  | nil =>
    intro ambient hidden
    let after := {ambient with steps := ambient.steps.push {
      decision := walk, outcome := false, netRx := ambient.netRxSection}}
    refine ⟨(false, table), after, ?_, rfl, rfl, hidden⟩
    simp [bucketWalk, branch, AmbientM.branch, after]
    rfl
  | cons e es ih =>
    intro ambient hidden
    let next := {ambient with steps := (ambient.steps.push {
      decision := walk, outcome := true, netRx := ambient.netRxSection}).push {
      decision := collide, outcome := e.index == index, netRx := ambient.netRxSection}}
    cases matched : e.index == index with
    | true =>
      refine ⟨(true, table), next, ?_, ?_, rfl, hidden⟩
      · rw [bucketWalk_cons]
        simp [branch, AmbientM.branch, matched, next]
        rfl
      · simp [matched]
    | false =>
      obtain ⟨⟨result, final⟩, after, run, found, state, hidden'⟩ :=
        ih next hidden
      refine ⟨(result, final), after, ?_, ?_, state, hidden'⟩
      · rw [bucketWalk_cons]
        simpa [StateT.run_bind, Except.bind, Except.map, branch, AmbientM.branch,
          matched, next] using run
      · simpa [matched] using found


theorem bucketHas_records_returns (walk collide : Decision) (index : Nat) (d : Device)
    (records : Option (List HiddenRecord)) (g : WGWorld) :
    Config.Product.Returns ((liftIndex (bucketHas walk collide index)).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = records)
      (fun (result, current) ambient => result = d.indexTable.any (·.index == index) ∧
        current.dev = some d ∧ ambient.hidden = records) := by
  intro ambient pre
  obtain ⟨⟨result, final⟩, after, run, found, same, hidden⟩ :=
    bucketWalk_records_returns walk collide index (bucket index d.indexTable)
      d.indexTable records ambient pre.2
  subst final
  refine ⟨(result, {g with dev := some d}), after, ?_, ?_, rfl, hidden⟩
  · rw [bucketHas_source]
    simp [liftIndex, getDev, pre.1, indexBucket, bucket, StateT.run_bind, modifyDev] at *
    rw [run]
    rfl
  · simpa [bucket_any] using found

theorem unhash_records_returns (decision : Decision) (owner : IndexOwner) (d : Device)
    (records : Option (List HiddenRecord)) (g : WGWorld) :
    Config.Product.Returns ((liftIndex (unhashEntry decision (·.owner == owner))).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = records)
      (fun (_, current) ambient =>
        current.dev = some {d with indexTable := removeOwner owner d.indexTable} ∧
        ambient.hidden = records) := by
  intro ambient pre
  let after := {ambient with steps := ambient.steps.push {
    decision, outcome := d.indexTable.any (·.owner == owner), netRx := ambient.netRxSection}}
  refine ⟨((), {g with dev := some {d with indexTable := removeOwner owner d.indexTable}}),
    after, ?_, rfl, pre.2⟩
  rw [liftIndex_run_variant, pre.1]
  simp [unhashEntry, removeOwner, after]
  rfl

theorem hiddenIndex_returns (draw : Draw) (rest : List HiddenRecord) (d : Device) (g : WGWorld) :
    Config.Product.Returns (((hidden .indexDraw : WG.M (List UInt8))).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some (draw.record :: rest))
      (fun (bytes, current) ambient =>
        bytes = draw.bytes ∧ current.dev = some d ∧ ambient.hidden = some rest) := by
  intro ambient pre
  refine ⟨(draw.bytes, g), {ambient with hidden := some rest}, ?_, rfl, pre.1, rfl⟩
  change ((AmbientM.hidden .indexDraw).run ambient).map
    (fun (bytes, after) => ((bytes, g), after)) = _
  rw [hiddenIndex_run ambient draw rest pre.2]
  rfl

end Leanux.Proofs.WG.Index
