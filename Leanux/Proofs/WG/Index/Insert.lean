import Leanux.Proofs.WG.Index.Collision
import Leanux.Proofs.WG.Noise.CryptoFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

abbrev unhashEntry := noise_const _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry
abbrev InsertState := Option Nat × Unit

def insertStep (owner : IndexOwner) (_ : Nat) (_ : InsertState) : M (ForInStep InsertState) := do
  let draw ← hidden .indexDraw
  let index := draw.foldr (fun b acc => acc * 256 + b.toNat) 0
  if ← bucketHas .idxInsWalk1 .idxInsCollide1 index then return .yield (none, ())
  if ← bucketHas .idxInsWalk2 .idxInsCollide2 index then
    unsupported "an index stolen during insertion"
  modifyDev fun d => { d with indexTable := { index, owner } :: d.indexTable }
  return .done (some index, ())

def insertFinish (state : InsertState) : M Nat := do
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

def InsertPost (owner : IndexOwner) (d : Device) (state : InsertState) (w : World) : Prop :=
  w.k.wg = some (insertedDevice owner d state.1) ∧
    ∀ n, state.1 = some n → d.indexTable.any (·.index == n) = false

theorem insertStep_spec (owner : IndexOwner) (turn : Nat) (state : InsertState) (d : Device) :
    Ensures (insertStep owner turn state) (fun w => w.k.wg = some d)
      (fun result w => match result with
        | .yield next => next = (none, ()) ∧ w.k.wg = some d
        | .done next => InsertPost owner d next w ∧ next.1 ≠ none) := by
  have hh := hidden_kernel_spec (fun k => k.wg = some d)
  have hb := fun walk collide index => (ensures_iff _ _ _).mp
    (show Ensures (bucketHas walk collide index) (fun w => w.k.wg = some d)
      (fun result w => result = d.indexTable.any (·.index == index) ∧ w.k.wg = some d) from by
        intro w result final pre run
        obtain ⟨r, v, hr, hpost⟩ := bucketHas_returns walk collide index d w pre
        rw [run] at hr
        cases hr
        exact hpost)
  rw [ensures_iff]
  mvcgen [insertStep, branch, modifyDev, modifyK, unsupported, hh, hb]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [InsertPost, insertedDevice]
  all_goals grind

def insertLoop (owner : IndexOwner) (turns : List Nat) : M InsertState :=
  forIn turns (none, ()) (insertStep owner)

theorem insertLoop_spec (owner : IndexOwner) (turns : List Nat) (d : Device) :
    Ensures (insertLoop owner turns) (fun w => w.k.wg = some d) (InsertPost owner d) := by
  induction turns with
  | nil =>
    rw [ensures_iff]
    simp [insertLoop, InsertPost, insertedDevice]
    mvcgen
    all_goals simp_all
  | cons turn turns ih =>
    intro w result final pre run
    simp only [insertLoop, List.forIn_cons, StateT.run_bind] at run
    cases first : (insertStep owner turn (none, ())).run w with
    | error err =>
      rw [first] at run
      change Except.error err = Except.ok (result, final) at run
      cases run
    | ok pair =>
      obtain ⟨step, middle⟩ := pair
      have hs := insertStep_spec owner turn (none, ()) d w step middle pre first
      rw [first] at run
      cases step with
      | done value =>
        change Except.ok (value, middle) = Except.ok (result, final) at run
        simp only [Except.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        exact hs.1
      | yield value =>
        obtain ⟨heq, hd⟩ := hs
        subst value
        exact ih middle result final hd run

theorem insertRange_spec (owner : IndexOwner) (budget : Nat) (d : Device) :
    Ensures (forIn ([:budget] : Std.Legacy.Range) (none, ()) (insertStep owner))
      (fun w => w.k.wg = some d) (InsertPost owner d) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact insertLoop_spec owner _ d

theorem insertFinish_spec (owner : IndexOwner) (state : InsertState) (d : Device) :
    Ensures (insertFinish state) (InsertPost owner d state)
      (fun index w => w.k.wg = some (insertedDevice owner d (some index)) ∧
        d.indexTable.any (·.index == index) = false) := by
  rw [ensures_iff]
  unfold insertFinish
  cases hs : state.1 <;>
    mvcgen [budgetExhausted, unsupported, invariant]
  all_goals simp_all [InsertPost]

theorem unhash_exact (decision : Decision) (owner : IndexOwner) (d : Device) :
    Ensures (unhashEntry decision (·.owner == owner)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with indexTable := removeOwner owner d.indexTable }) := by
  rw [ensures_iff]
  noise_vcgen [_private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry,
    getDev, getK, branch, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [removeOwner]

/-- A normally returning original insertion unhashes this owner first and
then inserts at a numeric index absent from the remaining table. -/
theorem indexInsert_exact (owner : IndexOwner) (d : Device) :
    Ensures (indexInsert owner) (fun w => w.k.wg = some d)
      (fun index w =>
        let remaining := removeOwner owner d.indexTable
        w.k.wg = some { d with indexTable := { index, owner } :: remaining } ∧
          remaining.any (·.index == index) = false) := by
  let removed := { d with indexTable := removeOwner owner d.indexTable }
  have hb : Ensures recordBudget (fun w => w.k.wg = some removed)
      (fun _ w => w.k.wg = some removed) := by
    rw [ensures_iff]
    mvcgen [recordBudget]
  rw [indexInsert_source]
  refine ensures_bind _ _ (unhash_exact .idxInsertHashed owner d) ?_
  intro u
  refine ensures_bind _ _ hb ?_
  intro budget
  refine ensures_bind _ _ (insertRange_spec owner budget removed) ?_
  intro state
  simpa [insertedDevice, removed] using insertFinish_spec owner state removed

end Leanux.Proofs.WG.Index
