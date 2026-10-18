import PairInsertSourceBucket

namespace Binary.Pair.Insert.Source
open Leanux Leanux.WG

def unhash (owner : IndexOwner) : M Unit := do
  _ ← branch .idxInsertHashed ((← getDev).indexTable.any (·.owner==owner))
  modifyDev fun d => {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}

/-- Expose the private bucket helper without changing the executable mirror.
The equality below is checked against the actual landed indexInsert definition. -/
def presentation (owner : IndexOwner) : M Nat := do
  unhash owner
  for _ in [0:(← recordBudget)] do
    let draw ← hidden .indexDraw
    let index := draw.foldr (fun b acc => acc*256+b.toNat) 0
    if ← hasBucket .idxInsWalk1 .idxInsCollide1 index then continue
    if ← hasBucket .idxInsWalk2 .idxInsCollide2 index then
      unsupported "an index stolen during insertion"
    modifyDev fun d => {d with indexTable := ⟨index,owner⟩::d.indexTable}
    return index
  budgetExhausted "index draws"

theorem indexInsert_eq (owner : IndexOwner) : WG.indexInsert owner=presentation owner := by
  rfl

def unlinkedWorld (w : World) (d : Device) (owner : IndexOwner) : World :=
  {w with
    k := {w.k with wg := some {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}}
    steps := w.steps.push {decision := .idxInsertHashed,outcome := d.indexTable.any (·.owner==owner),netRx := w.netRxSection}}

theorem unhash_run (w : World) (d : Device) (owner : IndexOwner) (device : w.k.wg=some d) :
    (unhash owner).run w=.ok ((),unlinkedWorld w d owner) := by
  simp [unhash,getDev,modifyDev,getK,modifyK,branch,unlinkedWorld,
    StateT.run_bind,StateT.run_pure,device]
  rfl

#print axioms indexInsert_eq
#print axioms unhash_run
end Binary.Pair.Insert.Source
