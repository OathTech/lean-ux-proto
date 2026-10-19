import SourceAdapter
import Leanux.WG.Peer

namespace Binary.LookupMirror
open Leanux Leanux.WG

abbrev Acc := Option IndexEntry × Bool

def record (w : World) (d : Decision) (b : Bool) : World :=
  {w with ambient := {w.ambient with steps := w.steps.push { decision := d, outcome := b, netRx := w.netRxSection }}}

def body (kinds : List IndexKind) (index : Nat)
    (e : IndexEntry) (a : Acc) : M (ForInStep Acc) := do
  _ ← branch .idxWalk true
  if ← branch .idxMatch (e.index == index) then
    let good ← branch .idxTypeMatch (kinds.contains e.kind)
    return .done (if good then some e else a.1, true)
  return .yield a

def scan (kinds : List IndexKind) (index : Nat) : List IndexEntry → Acc → World → Acc × World
  | [], a, w => (a, w)
  | e :: es, a, w =>
    let w := record w .idxWalk true
    let hit := e.index == index
    let w := record w .idxMatch hit
    if hit then
      let good := kinds.contains e.kind
      ((if good then some e else a.1, true), record w .idxTypeMatch good)
    else scan kinds index es a w

/-- Scanning changes only the decision log. This is equality of the entire
    World record, including supplied environment and all physical projections;
    it does not hide the remaining fields behind an unconstrained predicate. -/
theorem scan_world (kinds : List IndexKind) (index : Nat)
    (es : List IndexEntry) (a : Acc) (w : World) :
    (scan kinds index es a w).2 = {w with ambient := {w.ambient with steps := (scan kinds index es a w).2.steps}} := by
  induction es generalizing a w with
  | nil => rfl
  | cons e es ih =>
    by_cases hit : (e.index == index) = true
    · simp [scan, hit, record]
    · simp only [scan, hit, Bool.false_eq_true, ↓reduceIte]
      exact ih a (record (record w .idxWalk true) .idxMatch false)

#print axioms scan_world

/-- The operational bucket loop, including the exact ordered decisions.
    No distinct-index or successful-lookup assumption is used. -/
theorem loop_run (kinds : List IndexKind) (index : Nat)
    (es : List IndexEntry) (a : Acc) (w : World) :
    (forIn es a (body kinds index)).run w = .ok (scan kinds index es a w) := by
  induction es generalizing a w with
  | nil => rfl
  | cons e es ih =>
    cases hm : (e.index == index) <;> cases ht : (kinds.contains e.kind) <;>
      simp [List.forIn_cons, body, scan, hm, ht, Source.branch_run, record, StateT.run_bind, ih] <;> rfl

theorem loop_then {α} (kinds : List IndexKind) (index : Nat)
    (es : List IndexEntry) (a : Acc) (w : World) (finish : Acc → M α) :
    ((do let a ← forIn es a (body kinds index); finish a) : M α).run w =
      let out := scan kinds index es a w
      (finish out.1).run out.2 := by
  simp [StateT.run_bind, loop_run]

def sourceBody (kinds : List IndexKind) (index : Nat)
    (e : IndexEntry) (a : Acc) : M (ForInStep Acc) := do
  _ ← branch .idxWalk true
  if ← branch .idxMatch (e.index == index) then
    if ← branch .idxTypeMatch (kinds.contains e.kind) then
      return .done (some e, true)
    else return .done (a.1, true)
  else return .yield a

theorem sourceBody_eq_body (kinds : List IndexKind) (index : Nat) :
    sourceBody kinds index = body kinds index := by
  funext e a w
  cases hm : (e.index == index) <;> cases ht : (kinds.contains e.kind) <;>
    simp [sourceBody, body, branch, hm, ht] <;> rfl

def finish (a : Acc) : M (Option (IndexOwner × PeerId)) := do
  let entry := a.1
  let stopped := a.2
  if !stopped then _ ← branch .idxWalk false
  if ← branch .idxFound entry.isSome then
    let some e := entry | invariant "unreachable"
    let peer ← Source.peerGetMaybeZero (← (Source.peerWord e.owner))
    Source.setPeerWord e.owner peer
    if ← branch .idxPeerAlive peer.isSome then
      let some pid := peer | invariant "unreachable"
      return some (e.owner, pid)
  return none

/-- This equality checks that the recursive presentation is the actual
    executable mirror, including the suffix's fail-closed outcomes. -/
theorem indexLookup_eq (kinds : List IndexKind) (index : Nat) :
    Source.indexLookup kinds index = (do
      let es ← Source.indexBucket index
      let a ← forIn es (none, false) (body kinds index)
      finish a) := by
  rw [← sourceBody_eq_body]
  simp only [Source.indexLookup, WG.indexLookup, Source.liftWG_bind, Source.liftWG_forIn,
    Source.liftWG_pure, Source.liftWG_branch, apply_ite]
  congr 1
  funext es
  congr 1
  funext a
  rcases a with ⟨entry, stopped⟩
  cases entry <;> cases stopped <;>
    simp [finish, apply_ite]
  all_goals
    repeat' first | rfl | (apply Source.bind_congr_right; intro x) | split
  all_goals simp_all

theorem bucket_run (index : Nat) (w : World) (d : Device) (hd : w.wg.dev = some d) :
    (Source.indexBucket index).run w =
      .ok (d.indexTable.filter (fun e => e.index % 8192 == index % 8192), w) := by
  cases w with
  | mk ambient tasks seccomp fs wg fixture =>
    cases wg
    cases hd
    rfl

theorem indexLookup_run (kinds : List IndexKind) (index : Nat)
    (w : World) (d : Device) (hd : w.wg.dev = some d) :
    (Source.indexLookup kinds index).run w =
      let out := scan kinds index
        (d.indexTable.filter (fun e => e.index % 8192 == index % 8192)) (none, false) w
      (finish out.1).run out.2 := by
  rw [indexLookup_eq]
  simp only [StateT.run_bind, bucket_run index w d hd]
  change ((do
    let a ← forIn (d.indexTable.filter (fun e => e.index % 8192 == index % 8192))
      (none, false) (body kinds index)
    finish a) : M (Option (IndexOwner × PeerId))).run w = _
  exact loop_then _ _ _ _ _ _

#print axioms loop_run
#print axioms loop_then
#print axioms indexLookup_run
end Binary.LookupMirror
