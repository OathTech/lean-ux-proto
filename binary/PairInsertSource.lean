import SourceAdapter
import SourceIndex
import PairInsertSourceBucket

namespace Binary.Pair.Insert.Source
open Leanux Leanux.WG

def unhash (owner : IndexOwner) : M Unit := do
  _ ← branch .idxInsertHashed ((← Source.getDev).indexTable.any (·.owner==owner))
  Source.modifyDev fun d => {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}

/-- Expose the private bucket helper without changing the executable mirror.
The equality below is checked against the actual landed Source.indexInsert definition. -/
def presentation (owner : IndexOwner) : M Nat := do
  unhash owner
  for _ in [0:(← recordBudget)] do
    let draw ← hidden .indexDraw
    let index := draw.foldr (fun b acc => acc*256+b.toNat) 0
    if ← hasBucket .idxInsWalk1 .idxInsCollide1 index then continue
    if ← hasBucket .idxInsWalk2 .idxInsCollide2 index then
      unsupported "an index stolen during insertion"
    Source.modifyDev fun d => {d with indexTable := ⟨index,owner⟩::d.indexTable}
    return index
  budgetExhausted "index draws"

private def coreBucket (walk collide : Decision) (index : Nat) : IndexM Bool := do
  for e in ← WG.indexBucket index do
    _ ← branch walk true
    if ← branch collide (e.index == index) then return true
  _ ← branch walk false
  return false

private def coreUnhash (owner : IndexOwner) : IndexM Unit := do
  _ ← branch .idxInsertHashed ((← get).any (·.owner == owner))
  modify fun entries => entries.filter (fun e => !(e.owner == owner))

private def core (owner : IndexOwner) : IndexM Nat := do
  coreUnhash owner
  for _ in [0:(← recordBudget)] do
    let draw ← hidden .indexDraw
    let index := draw.foldr (fun b acc => acc*256+b.toNat) 0
    if ← coreBucket .idxInsWalk1 .idxInsCollide1 index then continue
    if ← coreBucket .idxInsWalk2 .idxInsCollide2 index then
      unsupported "an index stolen during insertion"
    modify fun entries => ⟨index,owner⟩::entries
    return index
  budgetExhausted "index draws"

private theorem core_eq (owner : IndexOwner) : WG.indexInsert owner = core owner := rfl

private theorem bucket_corr (walk collide : Decision) (index : Nat) :
    Binary.Source.Index.Corresponds (coreBucket walk collide index) (hasBucket walk collide index) := by
  unfold coreBucket hasBucket
  apply Binary.Source.Index.bind_corr (Binary.Source.Index.native_corr _)
  intro entries
  apply Binary.Source.Index.bind_corr
  · apply Binary.Source.Index.forIn_corr
    intro e a
    apply Binary.Source.Index.bind_corr (Binary.Source.Index.ambient_corr (AmbientM.branch walk true))
    intro _
    apply Binary.Source.Index.bind_corr (Binary.Source.Index.ambient_corr (AmbientM.branch collide (e.index == index)))
    intro hit
    cases hit <;> exact Binary.Source.Index.pure_corr _
  · intro a
    rcases a with ⟨answer, ⟨⟩⟩
    cases answer with
    | some value => exact Binary.Source.Index.pure_corr value
    | none =>
      apply Binary.Source.Index.bind_corr (Binary.Source.Index.ambient_corr (AmbientM.branch walk false))
      intro _
      exact Binary.Source.Index.pure_corr false

private theorem unhash_corr (owner : IndexOwner) :
    Binary.Source.Index.Corresponds (coreUnhash owner) (unhash owner) := by
  intro w d hd
  simp [coreUnhash, unhash, Source.getDev, Source.modifyDev, liftWG,
    WG.getDev, WG.modifyDev, StateT.run, bind, StateT.bind, StateT.lift,
    pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    liftM, monadLift, MonadLift.monadLift, liftAmbient, branch, AmbientM.branch,
    Except.pure, Except.bind, hd, Binary.Source.Index.install]


private theorem core_corr (owner : IndexOwner) :
    Binary.Source.Index.Corresponds (core owner) (presentation owner) := by
  unfold core presentation
  apply Binary.Source.Index.bind_corr (unhash_corr owner)
  intro _
  apply Binary.Source.Index.bind_corr (Binary.Source.Index.ambient_corr AmbientM.recordBudget)
  intro fuel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply Binary.Source.Index.bind_corr
  · apply Binary.Source.Index.forIn_corr
    intro i a
    apply Binary.Source.Index.bind_corr (Binary.Source.Index.ambient_corr (AmbientM.hidden .indexDraw))
    intro draw
    apply Binary.Source.Index.bind_corr (bucket_corr _ _ _)
    intro collision
    cases collision with
    | true => exact Binary.Source.Index.pure_corr _
    | false =>
      apply Binary.Source.Index.bind_corr (bucket_corr _ _ _)
      intro stolen
      cases stolen <;>
        repeat' first
          | exact Binary.Source.Index.pure_corr _
          | apply Binary.Source.Index.bind_corr (Binary.Source.Index.ambient_corr (AmbientM.unsupported "an index stolen during insertion")); intro _
          | apply Binary.Source.Index.bind_corr (Binary.Source.Index.modify_corr _); intro _
  · intro a
    rcases a with ⟨answer, ⟨⟩⟩
    cases answer with
    | some value => exact Binary.Source.Index.pure_corr value
    | none => exact Binary.Source.Index.ambient_corr (AmbientM.budgetExhausted "index draws")

theorem indexInsert_eq (owner : IndexOwner) : Source.indexInsert owner=presentation owner := by
  funext w
  change (Source.indexInsert owner).run w = (presentation owner).run w
  cases hd : w.wg.dev with
  | some d =>
    rw [core_corr owner w d hd]
    exact Binary.Source.Index.native_corr (core owner) w d hd
  | none =>
    simp [Source.indexInsert, presentation, unhash, Source.getDev, liftWG, liftIndex,
      WG.getDev, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, invariant, AmbientM.invariant,
      liftM, monadLift, MonadLift.monadLift, StateT.lift, Except.pure, Except.bind, hd]
    rfl

def unlinkedWorld (w : World) (d : Device) (owner : IndexOwner) : World :=
  {w with wg := {w.wg with dev := some {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}}, ambient := {w.ambient with steps := w.steps.push {decision := .idxInsertHashed,outcome := d.indexTable.any (·.owner==owner),netRx := w.netRxSection}}}

theorem unhash_run (w : World) (d : Device) (owner : IndexOwner) (device : w.wg.dev=some d) :
    (unhash owner).run w=.ok ((),unlinkedWorld w d owner) := by
  simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift, liftWG, liftAmbient, AmbientM.branch, WG.getDev, WG.modifyDev, unhash,Source.getDev,Source.modifyDev,Source.getWG,Source.modifyWG,branch,unlinkedWorld,
    StateT.run_bind,StateT.run_pure,device]

#print axioms indexInsert_eq
#print axioms unhash_run
end Binary.Pair.Insert.Source
