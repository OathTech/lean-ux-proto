import SourceAdapter
import MirrorPeer

namespace Binary.MirrorHistory
open Leanux Leanux.WG

inductive Tag where
  | decision (d : Decision)
  | call (symbol : String)
  | returned (symbol : String)
  deriving BEq, Repr

structure Point where
  tag : Tag
  world : World

abbrev Logged := StateT (List Point) M

def erase {α : Type} : Except Stop ((α × List Point) × World) → Except Stop (α × World)
  | .error e => .error e
  | .ok ((a, _), w) => .ok (a, w)

def Erases (logged : Logged α) (original : M α) : Prop :=
  ∀ history world, erase ((logged.run history).run world) = original.run world

theorem erases_pure (a : α) : Erases (pure a) (pure a) := by
  intro history world
  rfl

private theorem except_pure {α : Type} (a : α) : (pure a : Except Stop α) = .ok a := rfl

private theorem except_ok_bind {α β : Type} (a : α) (f : α → Except Stop β) :
    (Except.ok a >>= f) = f a := rfl

theorem erases_lift (a : M α) : Erases (StateT.lift a) a := by
  intro history world
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, except_pure]
  cases a.run world <;> rfl

private theorem error_bind {α β : Type} (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl

theorem erases_bind {logged : Logged α} {original : M α}
    {lg : α → Logged β} {og : α → M β}
    (ha : Erases logged original) (hb : ∀ a, Erases (lg a) (og a)) :
    Erases (logged >>= lg) (original >>= og) := by
  intro history world
  simp only [StateT.run_bind]
  have hm := ha history world
  cases he : (logged.run history).run world with
  | error e =>
    simp only [he, erase] at hm
    simp [← hm, erase, error_bind]
  | ok out =>
    rcases out with ⟨⟨a, h⟩, w⟩
    simp only [he, erase] at hm
    simpa [← hm, erase, except_ok_bind] using hb a h w

theorem erases_forIn (xs : List α) (b : β)
    (logged : α → β → Logged (ForInStep β))
    (original : α → β → M (ForInStep β))
    (h : ∀ a b, Erases (logged a b) (original a b)) :
    Erases (forIn xs b logged) (forIn xs b original) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using erases_pure b
  | cons a xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply erases_bind (h a b)
    intro s
    cases s with
    | done b => exact erases_pure b
    | yield b => exact ih b

/-- A mark reads the actual current World; its caller cannot supply a world
    or overwrite the history. Erasure alone would not guarantee log fidelity,
    so the concrete mark/run equations are also proved below. -/
def mark (tag : Tag) : Logged Unit := do
  let world ← StateT.lift (get : M World)
  modify (· ++ [⟨tag, world⟩])

theorem mark_run (tag : Tag) (history : List Point) (world : World) :
    ((mark tag).run history).run world = .ok (((), history ++ [⟨tag, world⟩]), world) := rfl

theorem mark_erases (tag : Tag) : Erases (mark tag) (pure ()) := by
  intro history world
  rfl

def called (symbol : String) (action : Logged α) : Logged α := do
  mark (.call symbol)
  let result ← action
  mark (.returned symbol)
  return result

theorem called_erases (symbol : String) (action : Logged α) (original : M α)
    (h : Erases action original) : Erases (called symbol action) original := by
  simpa only [called, pure_bind, bind_pure] using
    erases_bind (mark_erases (.call symbol)) (fun _ =>
      erases_bind h (fun result =>
        erases_bind (mark_erases (.returned symbol)) (fun _ => erases_pure result)))

def branchLogged (d : Decision) (b : Bool) : Logged Bool := do
  let answer ← StateT.lift (branch d b)
  mark (.decision d)
  return answer

theorem branch_erases (d : Decision) (b : Bool) :
    Erases (branchLogged d b) (branch d b) := by
  simpa only [branchLogged, pure_bind, bind_pure] using
    erases_bind (erases_lift (branch d b))
      (fun answer => erases_bind (mark_erases (.decision d))
        (fun _ => erases_pure answer))

theorem branch_run (d : Decision) (b : Bool) (history : List Point) (world : World) :
    ((branchLogged d b).run history).run world =
      let next := LookupMirror.record world d b
      .ok ((b, history ++ [⟨.decision d, next⟩]), next) := rfl

def branchCmpLogged (d : Decision) (b : Bool) (lhs rhs : Int) : Logged Bool := do
  let answer ← StateT.lift (branchCmp d b lhs rhs)
  mark (.decision d)
  return answer

theorem branchCmp_erases (d : Decision) (b : Bool) (lhs rhs : Int) :
    Erases (branchCmpLogged d b lhs rhs) (branchCmp d b lhs rhs) := by
  simpa only [branchCmpLogged, pure_bind, bind_pure] using
    erases_bind (erases_lift (branchCmp d b lhs rhs))
      (fun answer => erases_bind (mark_erases (.decision d))
        (fun _ => erases_pure answer))

theorem branchCmp_run (d : Decision) (b : Bool) (lhs rhs : Int)
    (history : List Point) (world : World) :
    ((branchCmpLogged d b lhs rhs).run history).run world =
      let next := PeerMirror.recordCmp world d b lhs rhs
      .ok ((b, history ++ [⟨.decision d, next⟩]), next) := rfl

def count (old : Nat) : Logged Bool := do
  if !(← branchCmpLogged .refcountAddNzZero (old == 0) old 0) then
    _ ← branchLogged .refcountAddNzRetry false
  if ← branchLogged .refcountAddNzNegative false then
    StateT.lift (unsupported "unreachable")
  if ← branchLogged .refcountAddNzWraps (old + 1 ≥ 2 ^ 31) then
    StateT.lift (unsupported "refcount_warn_saturate (overflow)")
  return old != 0

theorem count_erases (old : Nat) : Erases (count old) (refcountIncNotZero old) := by
  intro history world
  by_cases zero : old = 0 <;> by_cases wraps : old + 1 ≥ 2^31 <;>
    simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift, liftAmbient, AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported, count, refcountIncNotZero, branchCmpLogged, branchLogged, mark,
      branchCmp, branch, unsupported, erase, zero, wraps] <;> rfl

#print axioms branchCmp_run
#print axioms count_erases

def peerGet (peer : Option PeerId) : Logged (Option PeerId) := do
  if ← branchLogged .peerGetMaybeZeroNull peer.isNone then return none
  let some pid := peer | StateT.lift (invariant "unreachable")
  StateT.lift (Source.requireNotPending pid "a reference count the handshake worker also changes")
  let p ← StateT.lift (Source.getPeer pid)
  let live ← count p.refcount
  if ← branchLogged .peerGetMaybeZeroDead !live then return none
  StateT.lift (Source.setPeer pid {p with refcount := p.refcount + 1})
  return some pid

theorem peerGet_erases (peer : Option PeerId) :
    Erases (peerGet peer) (Source.peerGetMaybeZero peer) := by
  unfold peerGet Source.peerGetMaybeZero WG.peerGetMaybeZero
  simp only [Source.liftWG_bind, Source.liftWG_branch, Source.liftWG_pure, apply_ite]
  apply erases_bind (branch_erases _ _)
  intro null
  cases null with
  | true => exact erases_pure _
  | false =>
    cases peer with
    | none => exact erases_lift _
    | some pid =>
      simp only [Bool.false_eq_true, ↓reduceIte, Source.liftWG_bind, Source.liftWG_branch, Source.liftWG_pure, apply_ite]
      apply erases_bind (erases_lift _)
      intro _
      apply erases_bind (erases_lift _)
      intro p
      simp only [Source.liftWG_refcountIncNotZero]
      apply erases_bind (count_erases _)
      intro live
      apply erases_bind (branch_erases _ _)
      intro dead
      cases dead with
      | true => exact erases_pure _
      | false =>
        apply erases_bind (erases_lift _)
        intro _
        exact erases_pure _

#print axioms peerGet_erases

def body (kinds : List IndexKind) (index : Nat)
    (e : IndexEntry) (a : LookupMirror.Acc) : Logged (ForInStep LookupMirror.Acc) := do
  _ ← branchLogged .idxWalk true
  if ← branchLogged .idxMatch (e.index == index) then
    let good ← branchLogged .idxTypeMatch (kinds.contains e.kind)
    return .done (if good then some e else a.1, true)
  return .yield a

theorem body_erases (kinds : List IndexKind) (index : Nat)
    (e : IndexEntry) (a : LookupMirror.Acc) :
    Erases (body kinds index e a) (LookupMirror.body kinds index e a) := by
  unfold body LookupMirror.body
  apply erases_bind (branch_erases _ _)
  intro _
  apply erases_bind (branch_erases _ _)
  intro hit
  cases hit with
  | false => exact erases_pure _
  | true =>
    apply erases_bind (branch_erases _ _)
    intro good
    exact erases_pure _

theorem loop_erases (kinds : List IndexKind) (index : Nat)
    (es : List IndexEntry) (a : LookupMirror.Acc) :
    Erases (forIn es a (body kinds index)) (forIn es a (LookupMirror.body kinds index)) :=
  erases_forIn es a _ _ (body_erases kinds index)

def finish (a : LookupMirror.Acc) : Logged (Option (IndexOwner × PeerId)) := do
  let entry := a.1
  let stopped := a.2
  if !stopped then _ ← branchLogged .idxWalk false
  if ← branchLogged .idxFound entry.isSome then
    let some e := entry | StateT.lift (invariant "unreachable")
    let word ← StateT.lift (Source.peerWord e.owner)
    let peer ← called "wg_peer_get_maybe_zero" (peerGet word)
    StateT.lift (Source.setPeerWord e.owner peer)
    if ← branchLogged .idxPeerAlive peer.isSome then
      let some pid := peer | StateT.lift (invariant "unreachable")
      return some (e.owner, pid)
  return none

theorem finish_erases (a : LookupMirror.Acc) :
    Erases (finish a) (LookupMirror.finish a) := by
  unfold finish LookupMirror.finish
  cases stop : a.2 <;> simp only [stop, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  all_goals try (apply erases_bind (branch_erases .idxWalk false); intro _)
  all_goals
    apply erases_bind (branch_erases _ _)
    intro found
    cases found with
    | false => exact erases_pure _
    | true =>
      cases h : a.1 with
      | none =>
        apply erases_bind (erases_lift _)
        intro _
        exact erases_pure _
      | some e =>
        apply erases_bind (erases_lift _)
        intro word
        apply erases_bind (called_erases _ _ _ (peerGet_erases _))
        intro peer
        apply erases_bind (erases_lift _)
        intro _
        apply erases_bind (branch_erases _ _)
        intro alive
        cases alive with
        | false => exact erases_pure _
        | true =>
          cases peer with
          | none =>
            apply erases_bind (erases_lift _)
            intro _
            exact erases_pure _
          | some pid => exact erases_pure _

def lookup (kinds : List IndexKind) (index : Nat) : Logged (Option (IndexOwner × PeerId)) :=
  called "wg_index_hashtable_lookup" do
    let es ← StateT.lift (Source.indexBucket index)
    let a ← forIn es (none, false) (body kinds index)
    finish a

theorem lookup_erases (kinds : List IndexKind) (index : Nat) :
    Erases (lookup kinds index) (Source.indexLookup kinds index) := by
  rw [LookupMirror.indexLookup_eq]
  apply called_erases
  apply erases_bind (erases_lift _)
  intro es
  apply erases_bind (loop_erases kinds index es _)
  exact finish_erases

structure Run (α : Type) where
  result : α
  finalWorld : World
  points : List Point

def Accepted (logged : Logged α) (initial : World) (run : Run α) : Prop :=
  (logged.run []).run initial = .ok ((run.result, run.points), run.finalWorld)

theorem accepted_erases (logged : Logged α) (original : M α) (initial : World) (run : Run α)
    (erased : Erases logged original) (accepted : Accepted logged initial run) :
    original.run initial = .ok (run.result, run.finalWorld) := by
  have h := erased [] initial
  rw [accepted] at h
  exact h.symm

#print axioms lookup_erases
#print axioms accepted_erases

/-- Exact logged bucket execution, with each checkpoint holding the World
    immediately after that actual source branch records its decision. -/
def scan (kinds : List IndexKind) (index : Nat) :
    List IndexEntry → LookupMirror.Acc → List Point → World →
      (LookupMirror.Acc × List Point) × World
  | [], a, h, w => ((a, h), w)
  | e :: es, a, h, w =>
    let w₁ := LookupMirror.record w .idxWalk true
    let h₁ := h ++ [⟨.decision .idxWalk, w₁⟩]
    let hit := e.index == index
    let w₂ := LookupMirror.record w₁ .idxMatch hit
    let h₂ := h₁ ++ [⟨.decision .idxMatch, w₂⟩]
    if hit then
      let good := kinds.contains e.kind
      let w₃ := LookupMirror.record w₂ .idxTypeMatch good
      (((if good then some e else a.1, true), h₂ ++ [⟨.decision .idxTypeMatch, w₃⟩]), w₃)
    else scan kinds index es a h₂ w₂

theorem loop_run (kinds : List IndexKind) (index : Nat)
    (es : List IndexEntry) (a : LookupMirror.Acc) (history : List Point) (world : World) :
    ((forIn es a (body kinds index)).run history).run world =
      .ok (scan kinds index es a history world) := by
  induction es generalizing a history world with
  | nil => rfl
  | cons e es ih =>
    cases hm : (e.index == index) <;> cases ht : (kinds.contains e.kind) <;>
      simp [List.forIn_cons, body, scan, branchLogged, mark,
        LookupMirror.record, hm, ht, StateT.run_bind, StateT.run_lift, ih] <;> rfl


#print axioms loop_run

#print axioms mark_run
#print axioms branch_run
#print axioms loop_erases
end Binary.MirrorHistory
