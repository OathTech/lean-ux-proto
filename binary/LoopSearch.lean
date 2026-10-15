import MirrorHistory

namespace Binary.LookupSearch
open Leanux Leanux.WG

/-- The source segment corresponding to the entire binary bucket loop.
    Include found here: the compiler merges it with the terminal guard. -/
def searchPrefix (kinds : List IndexKind) (index : Nat) (es : List IndexEntry) :
    MirrorHistory.Logged (Option IndexEntry) := do
  let a ← forIn es (none, false) (MirrorHistory.body kinds index)
  if !a.2 then
    _ ← MirrorHistory.branchLogged .idxWalk false
  _ ← MirrorHistory.branchLogged .idxFound a.1.isSome
  return a.1

def finish (a : LookupMirror.Acc) (history : List MirrorHistory.Point) (w : World) :
    ((Option IndexEntry × List MirrorHistory.Point) × World) :=
  let w₁ := if a.2 then w else LookupMirror.record w .idxWalk false
  let h₁ := if a.2 then history else history ++ [⟨.decision .idxWalk, w₁⟩]
  let w₂ := LookupMirror.record w₁ .idxFound a.1.isSome
  ((a.1, h₁ ++ [⟨.decision .idxFound, w₂⟩]), w₂)

def result (kinds : List IndexKind) (index : Nat) (es : List IndexEntry)
    (history : List MirrorHistory.Point) (w : World) :=
  let out := MirrorHistory.scan kinds index es (none, false) history w
  finish out.1.1 out.1.2 out.2

theorem prefix_run (kinds : List IndexKind) (index : Nat) (es : List IndexEntry)
    (history : List MirrorHistory.Point) (w : World) :
    ((searchPrefix kinds index es).run history).run w = .ok (result kinds index es history w) := by
  unfold searchPrefix
  simp only [StateT.run_bind, MirrorHistory.loop_run]
  unfold result
  generalize MirrorHistory.scan kinds index es (none, false) history w = out
  rcases out with ⟨⟨⟨answer, stopped⟩, h⟩, world⟩
  cases stopped <;> rfl

/-- The empty case emits walk=false then found=false; it reads no peer. -/
theorem result_nil (kinds : List IndexKind) (index : Nat)
    (history : List MirrorHistory.Point) (w : World) :
    result kinds index [] history w = finish (none, false) history w := rfl

/-- A miss recurses on the actual tail with both decisions already logged. -/
theorem result_miss (kinds : List IndexKind) (index : Nat) (e : IndexEntry)
    (es : List IndexEntry) (history : List MirrorHistory.Point) (w : World)
    (miss : (e.index == index) = false) :
    result kinds index (e :: es) history w =
      let w₁ := LookupMirror.record w .idxWalk true
      let w₂ := LookupMirror.record w₁ .idxMatch false
      result kinds index es (history ++ [⟨.decision .idxWalk, w₁⟩] ++
        [⟨.decision .idxMatch, w₂⟩]) w₂ := by
  simp only [result, MirrorHistory.scan, miss, Bool.false_eq_true, ite_false]

/-- The first matching index terminates even when its kind is rejected. -/
theorem result_hit (kinds : List IndexKind) (index : Nat) (e : IndexEntry)
    (es : List IndexEntry) (history : List MirrorHistory.Point) (w : World)
    (hit : (e.index == index) = true) :
    result kinds index (e :: es) history w =
      let w₁ := LookupMirror.record w .idxWalk true
      let w₂ := LookupMirror.record w₁ .idxMatch true
      let good := kinds.contains e.kind
      let w₃ := LookupMirror.record w₂ .idxTypeMatch good
      finish (if good then some e else none, true)
        (history ++ [⟨.decision .idxWalk, w₁⟩] ++ [⟨.decision .idxMatch, w₂⟩] ++
          [⟨.decision .idxTypeMatch, w₃⟩]) w₃ := by
  simp only [result, MirrorHistory.scan, hit, ite_true]

/-- The complete source segment changes only the decision sequence. -/
theorem result_world (kinds : List IndexKind) (index : Nat) (es : List IndexEntry)
    (history : List MirrorHistory.Point) (w : World) :
    (result kinds index es history w).2 =
      {w with steps := (result kinds index es history w).2.steps} := by
  induction es generalizing history w with
  | nil => rfl
  | cons e es ih =>
    cases matchIndex : (e.index == index) with
    | false =>
      rw [result_miss kinds index e es history w matchIndex]
      exact ih _ _
    | true =>
      rw [result_hit kinds index e es history w matchIndex]
      rfl

/-- The suffix starts after the found decision. It retains the actual helper
    call and the peer-alive decision; it does not log found a second time. -/
def searchSuffix (entry : Option IndexEntry) : MirrorHistory.Logged (Option IndexEntry) := do
  match entry with
  | none => return none
  | some e =>
    let peer ← MirrorHistory.called "wg_peer_get_maybe_zero" (MirrorHistory.peerGet (some e.peer))
    if ← MirrorHistory.branchLogged .idxPeerAlive peer.isSome then return entry
    return none

/-- Splitting the terminal source code preserves its complete logged run,
    including failure, all Worlds and every call/decision checkpoint. -/
theorem finish_split (a : LookupMirror.Acc) :
    MirrorHistory.finish a = (do
      if !a.2 then
        _ ← MirrorHistory.branchLogged .idxWalk false
      _ ← MirrorHistory.branchLogged .idxFound a.1.isSome
      searchSuffix a.1) := by
  rcases a with ⟨entry, stopped⟩
  cases entry <;> cases stopped <;> rfl

/-- This is an equality with the actual logged lookup, not just with a
    separately defined source search. In particular its erasure is indexLookup. -/
theorem lookup_split (kinds : List IndexKind) (index : Nat) :
    MirrorHistory.lookup kinds index = MirrorHistory.called "wg_index_hashtable_lookup" (do
      let es ← StateT.lift (indexBucket index)
      let entry ← searchPrefix kinds index es
      searchSuffix entry) := by
  simp only [MirrorHistory.lookup, searchPrefix, finish_split, bind_assoc]
  congr 1
  congr 1
  funext es
  congr 1
  funext a
  cases a.2 <;> simp [bind_assoc]

#print axioms finish_split
#print axioms lookup_split

#print axioms prefix_run
#print axioms result_miss
#print axioms result_hit
#print axioms result_world
end Binary.LookupSearch
