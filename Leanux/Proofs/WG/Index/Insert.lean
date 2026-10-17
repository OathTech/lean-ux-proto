import Leanux.Proofs.WG.Index.Collision
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

abbrev unhashEntry := noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry
abbrev InsertState := Option Nat × Unit

def insertStep (owner : IndexOwner) (_ : Nat) (_ : InsertState) : IndexM (ForInStep InsertState) := do
  let draw ← hidden .indexDraw
  let index := draw.foldr (fun b acc => acc * 256 + b.toNat) 0
  if ← bucketHas .idxInsWalk1 .idxInsCollide1 index then return .yield (none, ())
  if ← bucketHas .idxInsWalk2 .idxInsCollide2 index then
    unsupported "an index stolen during insertion"
  modify fun table => { index, owner } :: table
  return .done (some index, ())

def insertFinish (state : InsertState) : IndexM Nat := do
  match state.1 with
  | some index => pure index
  | none => budgetExhausted "index draws"

theorem indexInsert_source (owner : IndexOwner) :
    indexInsert owner = (do
      unhashEntry .idxInsertHashed (·.owner == owner)
      let budget ← recordBudget
      let state ← forIn ([:budget] : Std.Legacy.Range) (none, ()) (insertStep owner)
      insertFinish state) := by
  simp only [indexInsert, insertFinish]
  congr 1
  funext u
  congr 1
  funext budget
  congr 1
  funext state
  cases state.1 <;> rfl

def insertedDevice (owner : IndexOwner) (d : Device) (index : Option Nat) : Device :=
  match index with
  | none => d
  | some n => { d with indexTable := { index := n, owner } :: d.indexTable }

def insertedTable (owner : IndexOwner) (table : List IndexEntry) (index : Option Nat) :
    List IndexEntry :=
  match index with
  | none => table
  | some n => {index := n, owner} :: table

def InsertPost (owner : IndexOwner) (table : List IndexEntry) (state : InsertState)
    (current : List IndexEntry) : Prop :=
  current = insertedTable owner table state.1 ∧
    ∀ n, state.1 = some n → table.any (·.index == n) = false

theorem insertStep_spec (owner : IndexOwner) (turn : Nat) (state : InsertState)
    (table : List IndexEntry) :
    Ensures (insertStep owner turn state) (fun t => t = table)
      (fun result t => match result with
        | .yield next => next = (none, ()) ∧ t = table
        | .done next => InsertPost owner table next t ∧ next.1 ≠ none) := by
  have hh : Ensures (hidden .indexDraw : IndexM (List UInt8)) (fun t => t = table)
      (fun _ t => t = table) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden .indexDraw) _)
  have hb (walk collide : Decision) (index : Nat) :
      Ensures (bucketHas walk collide index) (fun t => t = table)
        (fun result t => result = table.any (·.index == index) ∧ t = table) := by
    intro t ambient result final after ht hr
    subst t
    obtain ⟨actual, same, ambient', run, found, preserved⟩ :=
      bucketWalk_returns walk collide index (bucket index table) table table ambient rfl
    subst same
    have source : ((bucketHas walk collide index).run table).run ambient =
        .ok ((actual, table), ambient') := by
      rw [bucketHas_source]
      simpa [indexBucket, bucket] using run
    rw [source] at hr
    cases hr
    exact ⟨by simpa [bucket_any] using found, rfl⟩
  unfold insertStep
  refine ensures_bind _ _ hh ?_
  intro draw
  let index := draw.foldr (fun b acc => acc * 256 + b.toNat) 0
  refine ensures_bind _ _ (hb .idxInsWalk1 .idxInsCollide1 index) ?_
  intro first
  cases first with
  | true =>
    intro t ambient result final after pre run
    cases run
    exact ⟨rfl, pre.2⟩
  | false =>
    have second : Ensures (bucketHas .idxInsWalk2 .idxInsCollide2 index)
        (fun t => false = table.any (·.index == index) ∧ t = table)
        (fun result t => result = table.any (·.index == index) ∧
          t = table ∧ false = table.any (·.index == index)) := by
      intro t ambient result final after pre run
      have h := hb .idxInsWalk2 .idxInsCollide2 index t ambient result final after pre.2 run
      exact ⟨h.1, h.2, pre.1⟩
    refine ensures_bind _ _ second ?_
    intro found
    cases found with
    | true =>
      intro t ambient result final after pre _
      have impossible : true = false := pre.1.trans pre.2.2.symm
      cases impossible
    | false =>
      intro t ambient result final after pre run
      simp at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨⟨by simp [insertedTable, pre.2.1],
        by intro n hn; cases hn; exact pre.2.2.symm⟩, by simp⟩

def insertLoop (owner : IndexOwner) (turns : List Nat) : IndexM InsertState :=
  forIn turns (none, ()) (insertStep owner)

theorem insertLoop_spec (owner : IndexOwner) (turns : List Nat) (table : List IndexEntry) :
    Ensures (insertLoop owner turns) (fun t => t = table) (InsertPost owner table) := by
  induction turns with
  | nil =>
    intro t ambient result final after pre run
    cases run
    exact ⟨pre, by simp⟩
  | cons turn turns ih =>
    intro t ambient result final after pre run
    simp only [insertLoop, List.forIn_cons, StateT.run_bind] at run
    cases first : ((insertStep owner turn (none, ())).run t).run ambient with
    | error err =>
      rw [first] at run
      cases run
    | ok pair =>
      obtain ⟨⟨step, middle⟩, next⟩ := pair
      have hs := insertStep_spec owner turn (none, ()) table t ambient step middle next pre first
      rw [first] at run
      cases step with
      | done value =>
        change Except.ok ((value, middle), next) = Except.ok ((result, final), after) at run
        cases run
        exact hs.1
      | yield value =>
        obtain ⟨heq, ht⟩ := hs
        subst value
        exact ih middle next result final after ht run

theorem insertRange_spec (owner : IndexOwner) (budget : Nat) (table : List IndexEntry) :
    Ensures (forIn ([:budget] : Std.Legacy.Range) (none, ()) (insertStep owner))
      (fun t => t = table) (InsertPost owner table) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact insertLoop_spec owner _ table

theorem insertFinish_spec (owner : IndexOwner) (state : InsertState) (table : List IndexEntry) :
    Ensures (insertFinish state) (InsertPost owner table state)
      (fun index t => t = insertedTable owner table (some index) ∧
        table.any (·.index == index) = false) := by
  intro t ambient index final after pre run
  cases hs : state.1 with
  | none =>
    simp [insertFinish, hs, budgetExhausted, AmbientM.budgetExhausted,
      AmbientM.invariant, AmbientM.unsupported] at run
    split at run <;> cases run
  | some n =>
    simp [insertFinish, hs] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨by simpa [InsertPost, hs] using pre.1, pre.2 _ hs⟩

theorem unhash_exact (decision : Decision) (owner : IndexOwner) (table : List IndexEntry) :
    Ensures (unhashEntry decision (·.owner == owner)) (fun t => t = table)
      (fun _ t => t = removeOwner owner table) := by
  intro t ambient x final after pre run
  subst t
  let action : IndexM Unit := do
    _ ← branch decision (table.any (·.owner == owner))
    modify fun current => current.filter (fun e => !(e.owner == owner))
  change ((action.run table).run ambient) = _ at run
  simp [action, branch, AmbientM.branch] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  rfl

/-- A normally returning original insertion unhashes this owner first and
then inserts at a numeric index absent from the remaining table. -/
theorem indexInsert_exact (owner : IndexOwner) (d : Device) :
    Ensures (liftIndex (indexInsert owner)) (fun g => g.dev = some d)
      (fun index g =>
        let remaining := removeOwner owner d.indexTable
        g.dev = some { d with indexTable := { index, owner } :: remaining } ∧
          remaining.any (·.index == index) = false) := by
  have native : Ensures (indexInsert owner) (fun t => t = d.indexTable)
      (fun index t =>
        let remaining := removeOwner owner d.indexTable
        t = {index, owner} :: remaining ∧ remaining.any (·.index == index) = false) := by
    let removed := removeOwner owner d.indexTable
    have hb : Ensures (recordBudget : IndexM Nat) (fun t => t = removed)
        (fun _ t => t = removed) :=
      (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant AmbientM.recordBudget _)
    rw [indexInsert_source]
    refine ensures_bind _ _ (unhash_exact .idxInsertHashed owner d.indexTable) ?_
    intro u
    refine ensures_bind _ _ hb ?_
    intro budget
    refine ensures_bind _ _ (insertRange_spec owner budget removed) ?_
    intro state
    simpa [insertedTable, removed] using insertFinish_spec owner state removed
  intro g ambient index final after device run
  rw [liftIndex_run_variant, device] at run
  cases actual : ((indexInsert owner).run d.indexTable).run ambient with
  | error err => simp [actual, Except.map] at run
  | ok out =>
    rcases out with ⟨⟨n, table⟩, next⟩
    have h := native d.indexTable ambient n table next rfl actual
    simp [actual, Except.map] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨by simp [h.1], h.2⟩

end Leanux.Proofs.WG.Index
