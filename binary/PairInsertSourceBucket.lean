import SourceAdapter
import PairInsertInputProof
import MirrorLoop

namespace Binary.Pair.Insert.Source
open Leanux Leanux.WG

/-- The operational bucket walk used by the actual insertion. Its equality
inside Source.indexInsert is checked by the source-body normalization, not assumed. -/
def hasBucket (walk collide : Decision) (index : Nat) : M Bool := do
  for e in ← Source.indexBucket index do
    _ ← branch walk true
    if ← branch collide (e.index==index) then return true
  _ ← branch walk false
  return false

abbrev Acc := Option Bool × Unit

def walkBody (walk collide : Decision) (index : Nat) (e : IndexEntry) (_a : Acc) : M (ForInStep Acc) := do
  _ ← branch walk true
  if ← branch collide (e.index==index) then return .done (some true,())
  return .yield (none,())

def walkScan (walk collide : Decision) (index : Nat) : List IndexEntry → Acc → World → Acc × World
  | [],a,w => (a,w)
  | e::es,_a,w =>
    let w := LookupMirror.record w walk true
    let hit := e.index==index
    let w := LookupMirror.record w collide hit
    if hit then ((some true,()),w) else walkScan walk collide index es (none,()) w

theorem walkScan_world (walk collide : Decision) (index : Nat) (es : List IndexEntry) (a : Acc) (w : World) :
    (walkScan walk collide index es a w).2={w with ambient := {w.ambient with steps := (walkScan walk collide index es a w).2.steps}} := by
  induction es generalizing a w with
  | nil => rfl
  | cons e es ih =>
    by_cases hit : (e.index==index)=true
    · simp [walkScan,hit,LookupMirror.record]
    · simp only [walkScan,hit,Bool.false_eq_true,↓reduceIte]
      exact ih (none,()) (LookupMirror.record (LookupMirror.record w walk true) collide false)

theorem walk_run (walk collide : Decision) (index : Nat) (es : List IndexEntry) (a : Acc) (w : World) :
    (forIn es a (walkBody walk collide index)).run w=.ok (walkScan walk collide index es a w) := by
  induction es generalizing a w with
  | nil => rfl
  | cons e es ih =>
    cases hit : (e.index==index) <;>
      simp [List.forIn_cons,walkBody,walkScan,hit,LookupMirror.record,StateT.run_bind,ih] <;> rfl

def walkFinish (walk : Decision) (a : Acc) : M Bool :=
  match a.1 with
  | some answer => pure answer
  | none => do
    _ ← branch walk false
    return false

theorem hasBucket_eq (walk collide : Decision) (index : Nat) :
    hasBucket walk collide index=(do
      let entries ← Source.indexBucket index
      let a ← forIn entries (none,()) (walkBody walk collide index)
      walkFinish walk a) := by
  unfold hasBucket walkBody walkFinish
  congr 1
  funext entries
  congr 1
  funext a
  rcases a with ⟨answer,⟨⟩⟩
  cases answer <;> rfl

theorem walkScan_answer (walk collide : Decision) (index : Nat) (es : List IndexEntry) (w : World) :
    (walkScan walk collide index es (none,()) w).1=
      ((if es.any (·.index==index) then some true else none),()) := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    cases hit : (e.index==index) <;> simp [walkScan,hit,ih]

def bucketResult (walk collide : Decision) (index : Nat) (es : List IndexEntry) (w : World) : Bool × World :=
  let out := walkScan walk collide index es (none,()) w
  if es.any (·.index==index) then (true,out.2)
  else (false,LookupMirror.record out.2 walk false)

theorem bucketResult_world (walk collide : Decision) (index : Nat) (es : List IndexEntry) (w : World) :
    (bucketResult walk collide index es w).2={w with ambient := {w.ambient with steps := (bucketResult walk collide index es w).2.steps}} := by
  have frame := walkScan_world walk collide index es (none,()) w
  unfold bucketResult
  split
  · exact frame
  · simp only
    rw [frame]
    rfl

theorem hasBucket_run (walk collide : Decision) (index : Nat) (w : World) (d : Device)
    (device : w.wg.dev=some d) :
    (hasBucket walk collide index).run w=.ok (bucketResult walk collide index
      (d.indexTable.filter (fun e => e.index%8192==index%8192)) w) := by
  rw [hasBucket_eq]
  simp only [StateT.run_bind,LookupMirror.bucket_run index w d device]
  change ((do
    let a ← forIn (d.indexTable.filter (fun e => e.index%8192==index%8192))
      (none,()) (walkBody walk collide index)
    walkFinish walk a) : M Bool).run w=_
  rw [StateT.run_bind,walk_run]
  change (walkFinish walk (walkScan walk collide index _ (none,()) w).1).run
    (walkScan walk collide index _ (none,()) w).2=_
  rw [walkScan_answer]
  cases hit : (d.indexTable.filter (fun e => e.index%8192==index%8192)).any (·.index==index) <;>
    simp [walkFinish,bucketResult,hit,branch,LookupMirror.record] <;> rfl

theorem bucketResult_answer (walk collide : Decision) (index : Nat) (es : List IndexEntry) (w : World) :
    (bucketResult walk collide index es w).1=es.any (·.index==index) := by
  unfold bucketResult
  cases es.any (·.index==index) <;> rfl

theorem bucket_any (entries : List IndexEntry) (index : Nat) :
    (entries.filter (fun e => e.index%8192==index%8192)).any (·.index==index)=
      entries.any (·.index==index) := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    by_cases hit : e.index=index
    · simp [hit]
    · cases bucket : (e.index%8192==index%8192) <;>
        simp [bucket,hit,ih]

theorem hasBucket_effect {walk collide : Decision} {index : Nat} {w final : World} {d : Device} {answer : Bool}
    (device : w.wg.dev=some d) (accepted : (hasBucket walk collide index).run w=.ok (answer,final)) :
    answer=d.indexTable.any (·.index==index) ∧ final={w with ambient := {w.ambient with steps := final.steps}} := by
  rw [hasBucket_run walk collide index w d device] at accepted
  have equal := Except.ok.inj accepted
  have result := congrArg Prod.fst equal
  have state := congrArg Prod.snd equal
  dsimp only at result state
  constructor
  · rw [←result,bucketResult_answer,bucket_any]
  · have frame := bucketResult_world walk collide index
      (d.indexTable.filter (fun e => e.index%8192==index%8192)) w
    simpa only [state] using frame

/-- In the sequential source, the first walk changes only history. Its
miss therefore entails a miss in the locked walk, without a second-walk
outcome premise. The binary composition must establish the corresponding frame. -/
theorem second_walk_misses {index : Nat} {w middle : World} {d : Device}
    (device : w.wg.dev=some d)
    (first : (hasBucket .idxInsWalk1 .idxInsCollide1 index).run w=.ok (false,middle)) :
    ∃ final, (hasBucket .idxInsWalk2 .idxInsCollide2 index).run middle=.ok (false,final) ∧
      final={middle with ambient := {middle.ambient with steps := final.steps}} := by
  obtain ⟨empty,frame⟩ := hasBucket_effect device first
  have sameDevice : middle.wg.dev=some d := by rw [frame]; exact device
  let out := bucketResult .idxInsWalk2 .idxInsCollide2 index
    (d.indexTable.filter (fun e => e.index%8192==index%8192)) middle
  have answer : out.1=false := by rw [bucketResult_answer,bucket_any,←empty]
  refine ⟨out.2,?_,bucketResult_world _ _ _ _ _⟩
  rw [hasBucket_run _ _ _ _ d sameDevice]
  exact congrArg Except.ok (Prod.ext answer rfl)

#print axioms hasBucket_run
#print axioms bucketResult_world
#print axioms second_walk_misses
#print axioms walk_run
#print axioms hasBucket_eq
end Binary.Pair.Insert.Source
